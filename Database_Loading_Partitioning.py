#!/usr/bin/python
# -*- coding: utf-8 -*-

import psycopg2
import os
import StringIO

DATABASE_NAME = 'dds_assgn1'

def loadratings(ratingstablename, ratingsfilepath, openconnection):
    try:
        
        cursor = openconnection.cursor()
        # check if the table already exists and create if not
        cursor.execute("select count(*) from pg_tables where tablename='%s'" % ratingstablename)
        count = cursor.fetchone()
        if(count[0] == 0):
            print ("The table '%s' doesn't exist. Hence creating one" % ratingstablename)
            cursor.execute("create table %s (userid bigint, movieid bigint, rating float)" % ratingstablename)
        f1 = open(ratingsfilepath, 'r')        
        f2 = 0
        try:
            f2 = open('ratings.tmp', 'w')
        except IOError:
            for line in f1:
                tup = line.split("::")
                cursor.execute("insert into %s values(%s, %s, %s)" % (ratingstablename, tup[0], tup[1], tup[2]))
            f1.close()
            openconnection.commit()        
            return

        for line in f1:
            temp = line.split("::")
            f2.write(temp[0] + "," + temp[1] + "," + temp[2])
            f2.writelines('\n')
        f1.close()
        f2.close()
        
        f2 = open('ratings.tmp', 'r')
        cursor.copy_expert("COPY %s from STDIN with delimiter '%s'" % (ratingstablename,','),f2)
        f2.close()
        openconnection.commit()
        os.remove('ratings.tmp')
        
    except Exception as e:
        print (e)

def create_metatable(openconnection, ratingstablename):
    try:
        cursor = openconnection.cursor()
        cursor.execute("select count(*) from pg_tables where tablename='meta_table'")
        count = cursor.fetchone()
        if(count[0] == 0):
            cursor.execute("create table meta_table(tablename text, partitiontype text, partitioncount int, tabletracker int)" )
            cursor.execute("insert into meta_table values('', 'roundrobin', 0, 0)")
            cursor.execute("insert into meta_table values('', 'range', 0, 0)")
        openconnection.commit()
    except Exception as e:
        print (e)

def rangepartition(ratingstablename, numberofpartitions, openconnection):
    try:
        if numberofpartitions < 0 or not isinstance(numberofpartitions, int):
            print("Invalid partition count!")
            return
        
        create_metatable(openconnection, ratingstablename)
        cursor = openconnection.cursor()
        cursor.execute("create table range_master ( like %s including defaults including constraints including indexes)" % (ratingstablename))
        step = float(5.01) / float(numberofpartitions)
        low = 0.0
        partition_name = 1
        for i in [float(j) * step for j in range(1, numberofpartitions+1, 1)]:
            cursor.execute("create table range_part%s (check (rating >= %s AND rating < %s)) inherits (range_master)" % (partition_name, low, i))
            cursor.execute("insert into range_part%s select * from %s where (rating >= %s AND rating < %s)" % (partition_name, ratingstablename, low, i))
            low = i
            partition_name += 1

        cursor.execute("update meta_table set tablename = '%s', partitioncount = %d where partitiontype = 'range'" % (ratingstablename, numberofpartitions))

        # create trigger and procedure for handling future inserts
        query = "create or replace function range_part_insert_func() \
                 returns trigger as $$ \
                 begin "
        low = 0.0
        partition_name = 1
        for i in [float(j) * step for j in range(1, numberofpartitions+1, 1)]:
            if low == 0:
                query += "if "
            else:
                query += "elsif "
            query += "(new.rating >= %s AND new.rating < %s) then insert into range_part%s values (new.*); " % (low, i, partition_name)
            low = i
            partition_name += 1
        query += "end if; \
                  return null; \
                  end; \
                  $$ \
                  language plpgsql;"
        cursor.execute(query)

        cursor.execute("drop trigger if exists range_part_insert_trigger on range_master")
        cursor.execute("create trigger range_part_insert_trigger \
                        before insert on range_master \
                        for each row execute procedure range_part_insert_func()")

        openconnection.commit()
    except Exception as e:
        print (e)

def roundrobinpartition(ratingstablename, numberofpartitions, openconnection):
    try:
        if numberofpartitions < 0 or not isinstance(numberofpartitions, int):
            print("Invalid partition count!")
            return
        
        create_metatable(openconnection, ratingstablename)
        cursor = openconnection.cursor()
        round_robin_tracker = 0
        
        cursor.execute("create table roundrobin_master ( like %s including defaults including constraints including indexes)" % (ratingstablename))
        for i in range(0,numberofpartitions):
            cursor.execute("create table rrobin_part%s () inherits (roundrobin_master)" % (i))
            
        cursor.execute("select * from %s" % (ratingstablename))
        records = cursor.fetchall()

        chunksize = len(records) / numberofpartitions
        chunks = [records[x:x+chunksize] for x in xrange(0, len(records), chunksize)]
        for i in range(0, numberofpartitions):
            chunk = str(chunks[i]).replace("), (","\n").replace("[(","").replace(")]","").replace("L","")
            out = StringIO.StringIO()
            out.write(chunk)
            out.seek(0)
            cursor.copy_from(out,"rrobin_part%s" % (i), ',', columns=('userid','movieid','rating'))
            out.close()

        leftover = len(records) - (numberofpartitions * chunksize)
        for i in range((len(records) - leftover), len(records)):
            cursor.execute("insert into rrobin_part%s values(%s, %s, %s)" % (round_robin_tracker, records[i][0], records[i][1], records[i][2]))
            round_robin_tracker = (round_robin_tracker+1)%numberofpartitions

        cursor.execute("update meta_table set tablename = '%s', partitioncount = %d, tabletracker = %d where partitiontype = 'roundrobin'" % (ratingstablename, numberofpartitions, round_robin_tracker))
        openconnection.commit()
        
    except Exception as e:
        print (e)

def roundrobininsert(ratingstablename, userid, itemid, rating, openconnection):
    try:
        if (rating > 5 or rating < 0):
            print("Attempt to insert an incorrect Rating value!")
            return

        cursor = openconnection.cursor()
        cursor.execute("select partitioncount, tabletracker from meta_table where partitiontype='roundrobin'")
        record = cursor.fetchone()
        partitioncount = record[0]
        if partitioncount == 0:
            print("There are no partitions! Inserting into the parent table")
            cursor.execute("insert into %s values(%s, %s, %s)" % (ratingstablename, userid, itemid, rating))
            return
        round_robin_tracker = record[1]
        
        cursor.execute("insert into rrobin_part%s values(%s, %s, %s)" % (round_robin_tracker, userid, itemid, rating))
        round_robin_tracker = (round_robin_tracker+1)%partitioncount

        cursor.execute("update meta_table set tabletracker = %d where partitiontype = 'roundrobin'" % (round_robin_tracker))
        openconnection.commit()
        
    except Exception as e:
        print (e)

def rangeinsert(ratingstablename, userid, itemid, rating, openconnection):
    try:
        if (rating > 5 or rating < 0):
            print("Attempt to insert an incorrect Rating value!")
            return
        
        cursor = openconnection.cursor()
        cursor.execute("select partitioncount from meta_table where partitiontype='range'")
        record = cursor.fetchone()
        partitioncount = record[0]
        if partitioncount == 0:
            print("There are no partitions! Inserting into the parent table")
            cursor.execute("insert into %s values(%s, %s, %s)" % (ratingstablename, userid, itemid, rating))
            return

        cursor.execute("insert into range_master values(%s, %s, %s)" % (userid, itemid, rating))
        openconnection.commit()
    except Exception as e:
        print (e)

def deletepartitionsandexit(openconnection):
    try:
        cursor = openconnection.cursor()
        cursor.execute("drop table meta_table")

        cursor.execute("select count(*) from pg_tables where tablename like 'roundrobin_master'")
        count = cursor.fetchone()
        if(count[0] == 1):
            cursor.execute("drop table roundrobin_master cascade")

        cursor.execute("select count(*) from pg_tables where tablename like 'range_master'")
        count = cursor.fetchone()
        if(count[0] == 1):
            cursor.execute("drop table range_master cascade")

        openconnection.commit()
    except Exception as e:
        print (e)

# Middleware
def before_db_creation_middleware():
    pass

def after_db_creation_middleware(databasename):
    pass

def before_test_script_starts_middleware(openconnection, databasename):
    pass

def after_test_script_ends_middleware(openconnection, databasename):
    pass
    

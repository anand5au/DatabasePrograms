import psycopg2
import os
import sys

def WriteTuplesToFile(cursor, fp, ratingMinValue, ratingMaxValue, part_name, part_count, query_type):
    if (part_count > 0):
            for i in range(0,part_count):
                query_table = part_name+str(i)
                if(query_type == "range"):
                    cursor.execute("select * from %s where rating >= %s and rating <= %s" % (query_table, ratingMinValue, ratingMaxValue))
                elif(query_type == "point"):
                    cursor.execute("select * from %s where rating = %s" % (query_table, ratingMinValue))
                else:
                    cursor.execute("select * from %s" % (query_table))
                rows = cursor.fetchall()
                for row in rows:
                    row = str(row).replace("(","").replace(")","")
                    row = query_table + ", " + row
                    fp.write(row)
                    fp.writelines('\n')

def RangeQuery(ratingsTableName, ratingMinValue, ratingMaxValue, openconnection):
    try:
        cursor = openconnection.cursor()
        cursor.execute("select count(*) from rangeratingsmetadata")
        part_count = int(str(cursor.fetchone()).replace("(","").replace("L,)",""))
        try:
            f = open('RangeQueryOut.txt','a')
            f.truncate()
            WriteTuplesToFile(cursor,f,ratingMinValue, ratingMaxValue,"rangeratingspart",part_count,"range")
            cursor.execute("select partitionnum from roundrobinratingsmetadata")
            part_count = int(str(cursor.fetchone()).replace("(","").replace(",)",""))
            WriteTuplesToFile(cursor,f,ratingMinValue, ratingMaxValue,"roundrobinratingspart",part_count,"range")
            f.close()
        except IOError:
            print ("Error in File operation")
    except Exception as e:
        print (e)


def PointQuery(ratingsTableName, ratingValue, openconnection):
    try:
        cursor = openconnection.cursor()
        cursor.execute("select count(*) from rangeratingsmetadata")
        part_count = int(str(cursor.fetchone()).replace("(","").replace("L,)",""))
        try:
            f = open('PointQueryOut.txt','a')
            f.truncate()
            WriteTuplesToFile(cursor,f,ratingValue, ratingValue,"rangeratingspart",part_count,"point")
            cursor.execute("select partitionnum from roundrobinratingsmetadata")
            part_count = int(str(cursor.fetchone()).replace("(","").replace(",)",""))
            WriteTuplesToFile(cursor,f,ratingValue, ratingValue,"roundrobinratingspart",part_count,"point")
            f.close()
        except IOError:
            print ("Error in File operation")
    except Exception as e:
        print (e)

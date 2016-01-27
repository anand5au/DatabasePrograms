#!/usr/bin/python2.7
#
# Assignment5 Interface
# Name: Anand Kumar Dhandapani
#

from pymongo import MongoClient
import os
import sys
import json
import re
import codecs
import math

def distance_in_miles(lat1, lon1, lat2, lon2):
    R = 3959
    t1 = math.radians(lat1)
    t2 = math.radians(lat2)
    dt = math.radians(lat2-lat1);
    dl = math.radians(lon2-lon1);

    a = math.sin(dt/2) * math.sin(dt/2) + math.cos(t1) * math.cos(t2) * math.sin(dl/2) * math.sin(dl/2);
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1-a));
    d = R * c;
    return d

def FindBusinessBasedOnCity(cityToSearch, saveLocation1, collection):
    cursor = collection.find({"city":re.compile(cityToSearch, re.IGNORECASE)})
    try:
        f = codecs.open(saveLocation1,'a', encoding='utf-8')
        f.truncate()
        for result in cursor:
            line = "%s$%s$%s$%s\n" % (result["name"].upper(), result["full_address"].upper().replace("\n",","), result["city"].upper(), result["state"].upper())
            f.write(line)
            #print line
    except Exception as e:
        print e

def FindBusinessBasedOnLocation(categoriesToSearch, myLocation, maxDistance, saveLocation2, collection):
    lat = myLocation[0]
    lon = myLocation[1]
    cursor = collection.find({"categories": {"$in":categoriesToSearch}})
    try:
        f = codecs.open(saveLocation2,'a', encoding='utf-8')
        f.truncate()
        for result in cursor:
            dist = distance_in_miles(float(lat), float(lon), float(result["latitude"]), float(result["longitude"]))
            #print dist
            if dist <= maxDistance:
                line = "%s\n" % result["name"].upper()
                f.write(line)
    except Exception as e:
        print e

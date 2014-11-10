#!/bin/bash

java \
-cp bin:lib/mailapi.jar:lib/bcprov-jdk15on-147.jar:lib/smtp.jar:/home/bart/Documents/paragon/lib \
se.chalmers.parajpmail.SendMail
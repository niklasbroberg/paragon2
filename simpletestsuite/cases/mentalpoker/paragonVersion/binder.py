#!/usr/bin/python
# binder.py
# Process coordinator for mental poker jif implementation
# Author: Aslan Askarov, aaskarov@cs.chalmers.se


import os
import sys
import thread
import threading
import popen2
import select

r,w = os.pipe()
# semaphore provides readable and not thread mixed output to the console
screen = threading.Semaphore() 

def box( ii, oo ):
    i = ii.fileno()
    o = oo.fileno()
    
    nlink = 0
    
    
    data  = ''
    lines = []
    
    while not data.startswith('###'):
        while not lines or not lines[0].endswith('\n'):
            # read next chunk of raw data from the file
            rawdata = os.read(i, 16384)
            # split it apart
            newlines = rawdata.splitlines(True)
            if lines:
                lines[0] += newlines[0]
                lines+=newlines[1:]
            else:
                lines = newlines
                                   
        data = lines[0]
        lines = lines[1:]
    
        # just write out debugging information
        if not data.startswith('###'):
            screen.acquire()
            print "::", threading.currentThread().getName(), repr(data)
            sys.stdout.flush()
            screen.release()
    # by now we get the first non debug value in the input
    
    if data.startswith('###DNCLINK'):
        nlink+=1
        
    
    buf = data
    total = len (buf)
    
    screen.acquire()
    # print "-", threading.currentThread().getName(),
    # print "", len(data), "bytes",
    # print "uffer is", len(buf), "bytes",
    # print "otal read", total, 
    # print "link", nlink
    sys.stdout.flush()
    screen.release()
    
    neof = True
    noex = True
    
    # keep looping until we have something to read
    while neof:
        # enter the loop if we either have no buffered lines 
        # at all, or it doesn't end with newline
        while not lines or not lines[0].endswith('\n'):
            if buf and noex:
                owth = [o]
            else:
                owth = []
        
            a, b, _ = select.select ([i], owth, [])
            
            if b: # there is a place for us to write
                try:
                    n = os.write(o,buf)        # non-blocking write       
                    oo.flush()
                    buf = buf[n:]
                    screen.acquire()
                    # print "-", threading.currentThread().getName(), 
                    # print "", n, "bytes",
                    # print "uffer is", len(buf), "bytes"  
                    sys.stdout.flush()
                    screen.release()
                        
                except OSError, detail:
                    screen.acquire()
                    # print "*", threading.currentThread().getName(), 
                    print 'OSError:', detail
                    sys.stdout.flush()
                    screen.release()
                    noex = False
                        
            if a:
                # we have something to read
                # read the next chunk of raw data from the file                
                
                rawdata = os.read(i, 16384)
                # check for EOF
                if not rawdata:
                    screen.acquire()
                    # print "-", threading.currentThread().getName(),
                    # print "OF"
                    sys.stdout.flush()
                    screen.release()
                    neof = False
                    break
                
                # split the raw data apart
                newlines = rawdata.splitlines(True)
                if lines:
                    lines[0] += newlines[0]
                    lines+=newlines[1:]
                else:
                    lines = newlines
        if not neof:
            break             
        data = lines[0]
        lines = lines[1:]
        
        # we actually got a line in data at this point
        # process it
        if not data.startswith("###"):
            screen.acquire()
            print "::", threading.currentThread().getName(), repr(data)
            sys.stdout.flush()
            screen.release()                
            continue

        if data.startswith('###DNCLINK'):
            nlink+=1

        # if data.startswith('###DATAFIELD'):
            # screen.acquire()
            # print "::", threading.currentThread().getName(), repr(data)
            # sys.stdout.flush()
            # screen.release()
        # screen.acquire()
        # print "::", threading.currentThread().getName(), repr(data[:10]),
        # # print "..", repr(data)[(len(data)-6):]
        # screen.release()

        
        buf += data
        #neof = data
        
        total += len(data)
        screen.acquire()
        # print "-", threading.currentThread().getName(),
        # print "", len(data), "bytes",
        # print "uffer is", len(buf), "bytes",
        # print "otal read", total,
        # print "link", nlink
        sys.stdout.flush()
        screen.release()
        ## print "-", threading.currentThread().getName(), repr(data)      
       
        
    # eof is reached, just flush out the rest of the buffer
    
    # while we have something to tell and there is someone 
    # who wants to listen to us
    while buf and noex:
        try:
            screen.acquire()
            # print "-", threading.currentThread().getName(), 
            # print "aiting for channel"
            sys.stdout.flush()
            screen.release()
            a,b,_ = select.select ([r], [o], [])
            if b:                    
                n = os.write(o, buf) # non blocking write
                oo.flush()     # not sure if this is really required
                screen.acquire()
                # print "-", threading.currentThread().getName(), 
                # print "rote ", n, "bytes"
                sys.stdout.flush()
                screen.release()
                buf = buf[n:]
            if a:
                screen.acquire()
                # print "-", threading.currentThread().getName(),
                # print "ot signal to leave"
                sys.stdout.flush()
                screen.release()
                break
        except OSError, detail:
            screen.acquire()
            # print "*", threading.currentThread().getName(), 
            print 'OSError:', detail
            sys.stdout.flush()
            screen.release()
            noex = False
    screen.acquire()
    # print "-",  threading.currentThread().getName(), "Finished"
    sys.stdout.flush()
    screen.release()    
    # signal the other thread that we are leaving...
    # so that it gets unblocked and quits as well
    os.write(w, threading.currentThread().getName())
    # # print "-",  threading.currentThread().getName(), "Semaphore released"    

#

print "++", "starting ..."
# oleft,  ileft , eleft = popen2.popen3('jif -cp .:../../jif-1.1.1/rt-classes:../../jif-1.1.1/lib-classes -Djava.library.path=../../jif-1.1.1/lib  mp/Main Alice')
oleft,  ileft , eleft = popen2.popen3('java -cp bin:lib/paragonRT.jar mp/Main Alice')
# oright, iright, eright = popen2.popen3('jif -cp .:../../jif-1.1.1/rt-classes:../../jif-1.1.1/lib-classes -Djava.library.path=../../jif-1.1.1/lib  mp/Main Bob')
oright, iright, eright = popen2.popen3('java -cp bin:lib/paragonRT.jar  mp/Main Bob')

left  = threading.Thread(None, box, "L",  [oleft, iright])
right = threading.Thread(None, box, "R", [oright, ileft])

# starting threads
left.start()
right.start()

left.join()
right.join()
print "++", "all done."



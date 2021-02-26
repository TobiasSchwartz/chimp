##################
# Reserved words #
################################################################
# HybridHTNDomain                                              #
# MaxArgs                                                      #
# :operator                                                    #
# :method                                                      #
# Head                                                         #
# Pre                                                          #
# Add                                                          #
# Del                                                          #
# Sub                                                          #
# Constraint                                                   #
# Ordering                                                     #
# Type                                                         #
# Values                                                       #
# StateVariable                                                #
# FluentResourceUsage                                          #
# Param                                                        #
# ResourceUsage                                                #
# Usage                                                        #
# Resource                                                     #
# Fluent                                                       #
#                                                              #
##   All AllenIntervalConstraint types                         #
##   '[' and ']' should be used only for constraint bounds     #
##   '(' and ')' are used for parsing                          #
#                                                              #
################################################################

# A clone of the original RACE domain

(HybridHTNDomain TrainDomain)

(MaxArgs 5)

(PredicateSymbols TrainAt SignalAt Connected Type SignalBlocked Visited
 !wait !drive_connection !drive_to_next_signal
  request_signal !free_signal !block_signal
  drive drive_segment
  Future
  Eternity)


(Resource navigationCapacity 1)
(Resource segmentCapacity 1)
##
# (Resource fuelTank1 1)

(StateVariable TrainAt 2 n)
(StateVariable SignalAt 1 signal1 signal2 signal3 signal4)


################################
####  OPERATORS ################

# DRIVE_SEGMENT 
# drive from current position to the next free signal
(:operator
 (Head !drive_through_segment(?train ?toSignal))
 (Pre p1 TrainAt(?train ?fromSignal))
 # (Pre p2 SignalFree(?fromSignal))
 # (Pre p3 SignalFree(?toSignal))
 (Pre p4 SignalAt(?fromSignal ?origin))
 (Pre p5 SignalAt(?toSignal ?dst))
 (Pre p6 Connected(?origin ?x))
 (Pre p7 Connected(?x ?dst))
 (Constraint OverlappedBy(task,p1))
 (Constraint Duration[2000,INF](task))
 (Add e1 TrainAt(?train ?toSignal))
 (Add e2 Driving(?train))
 (Constraint Overlaps(task,e1))
 (Constraint During(task,e2))  # Drive the whole segment without a break
 (Del p1) (Del p2)
 (ResourceUsage 
    (Usage segmentCapacity 1))
)

# DRIVE_SEGMENT 
# drive from current position to the next red signal and thus stop
(:operator
 (Head !drive_segment_stop(?train ?toSignal))
 (Pre p1 TrainAt(?train ?fromSignal))
 (Pre p2 SignalFree(?fromSignal))
 (Pre p3 SignalFree(?toSignal))
 (Pre p4 Connected(?fromSignal ?toSignal))
 (Constraint OverlappedBy(task,p1))
 (Constraint Duration[3000,INF](task))
 (Add e1 TrainAt(?train ?toSignal))
 (Add e2 Driving(?train))
 (Constraint Overlaps(task,e1))
 (Constraint OverlappedBy(task,e2))
 # (Constraint EndsDuring(e2, task))
 (Del p1) (Del p2) (Del e2)
 (ResourceUsage 
    (Usage segmentCapacity 1))
)

## REQUEST / RELEASE signal
(:method #already granted access
  (Head request_signal(?train ?signal))
  (Pre p1 SignalBlocked(?signal ?train))
  (Constraint Duration[2,INF](task)) 
)

(:method #requesting new signal
  (Head request_signal(?train ?signal))
  (Pre p1 SignalBlocked(?signal ?none))
  (Values ?none nobody) # signal blocked by nobody
  
  (Sub s1 !block_signal(?train ?signal)) # request signal
  (Constraint Duration[5,INF](task)) 
)

(:method #wait for signal
  (Head request_signal(?train ?signal))
  (Pre p1 SignalBlocked(?signal ?other))
  (VarDifferent ?other ?train) # signal blocked by someone else
  (Pre p2 TrainAt(?train ?sig))
  
  (Sub s1 !wait(?train ?sig)) # wait some time at current location
  (Sub s2 request_signal(?train ?signal)) # request signal again

  (Ordering s1 s2)
  (Constraint Before(s1,s2))
)

(:method #requesting signal for first time at all
  (Head request_signal(?train ?signal))

  
  (Sub s1 !block_signal(?train ?signal)) # request signal
  (Constraint Duration[5,INF](task)) 
)

(:operator
  (Head !block_signal(?signal ?train))
  (Add e1 SignalBlocked(?signal ?train))
)
 
 
(:operator #empty signal not needed anymore
  (Head !free_signal(?train ?signal))
  (Pre p1 SignalBlocked(?signal ?train))
  (Add e1 SignalBlocked(?signal nobody))
  (Constraint Duration[5,INF](task)) 
)

## Do nothing, just wait at a signal
(:operator
  (Head !wait(?train ?signal))
  (Pre p1 TrainAt(?train ?signal))
  (Constraint Duration[1000,INF](task))
  (Constraint During(task,p1)) #train should wait at the signal the whole time
)

## DRIVE operation
# normal driving between two directly connected points
(:operator
  (Head !drive_connection(?train ?currentPos ?nextPos))
  (VarDifferent ?currentPos ?nextPos)
  (Pre p1 TrainAt(?train ?currentPos))
  (Pre p2 not(Visited(?train ?nextPos)))
  (Pre p4 Connected(?currentPos ?nextPos))
  (Add e1 TrainAt(?train ?nextPos))
  (Add e2 Visited(?train ?nextPos))
  (Constraint Duration[1000,INF](task))
  (Del p1)
)

# normal driving between two directly connected points
# where the train currently is at a signal at the starting position 
(:operator
  (Head !drive_connection(?train ?currentPos ?nextPos))
  (VarDifferent ?currentPos ?nextPos)
  (Pre p1 TrainAt(?train ?currentSignal))
  (Pre p2 Not Visited(?train ?nextPos))
  (Pre p3 SignalAt(?currentSignal ?currentPos))
  (Pre p4 Connected(?currentPos ?nextPos))
  
  (Add e1 TrainAt(?train ?nextPos))
  (Add e2 Visited(?train ?nextPos))
  (Constraint Duration[1000,INF](task))
  (Del p1)
)

## DRIVE operation
# drive segment finished
(:method 
  (Head drive_segment(?train ?currentSignal ?currentSignal))
#  (Pre p0 Type(?train Train))
  (Pre p1 TrainAt(?train ?currentSignal))
  (Constraint During(task,p1))
  (Constraint Duration[1,1](task))
)

# drive segment finished
(:method
  (Head drive_segment(?train ?currentPos ?currentSignal))
#  (Pre p0 Type(?train Train))
  (Pre p1 TrainAt(?train ?currentPos))
  (Pre p2 SignalAt(?currentSignal ?currentPos))
  (Constraint During(task,p1))
  (Constraint Duration[1,1](task))
)

# normal driving from a signal to the next signal
(:method
  (Head drive_segment(?train ?currentPos ?nextSignal))
  (VarDifferent ?currentPos ?nextSignal)
#  (Pre p0 Type(?train Train))

  (Pre p4 TrainAt(?train ?currentPos))
  (Pre p5 SignalAt(?currentPos ?l1))
  (Pre p6 Connected(?l1 ?l2))
  
  (Sub s1 !drive_connection(?train ?l1 ?l2))
#  (Sub s2 drive_segment(?train ?l2 ?nextSignal))

#  (Ordering s1 s2)
#  (Constraint BeforeOrMeets(s1,s2))
)

# normal driving from a signal to the next signal
(:method
  (Head drive_segment(?train ?currentPos ?nextSignal))
  (VarDifferent ?currentPos ?nextSignal)
#  (Pre p0 Type(?train Train))

  (Pre p2 SignalAt(?currentSignal ?currentPos))
  (Pre p3 TrainAt(?train ?currentSignal))
  (Pre p6 Connected(?currentPos ?nextPos))
  
  (Sub s1 !drive_connection(?train ?currentPos ?nextPos))
#  (Sub s2 drive_segment(?train ?nextPos ?nextSignal))

#  (Ordering s1 s2)
#  (Constraint BeforeOrMeets(s1,s2))
)

# normal driving from a position on the track segment to the next signal
(:method
  (Head drive_segment(?train ?currentPos ?nextSignal))
  (VarDifferent ?currentPos ?nextSignal)
#  (Pre p0 Type(?train Train))
#  (Pre p0 NotType(?currentPos entry))
#  (Pre p1 NotType(?signalType signals))
#  (Pre p2 Type(?nextSignal ?signalType2))
#  (Pre p3 Type(?signalType2 signals))

  (Pre p4 TrainAt(?train ?currentPos))
  (Pre p5 Connected(?currentPos ?nextPos))
  
  (Sub s1 !drive_connection(?train ?currentPos ?nextPos))
#  (Sub s2 drive_segment(?train ?nextPos ?nextSignal))

#  (Ordering s1 s2)
#  (Constraint BeforeOrMeets(s1,s2))
)

# driving into a halt signal
#(:method
#  (Head !drive_segment(?train ?currentSignal ?nextSignal))
#  (VarDifferent ?currentSignal ?nextSignal)
#  (Pre p0 Type(?nextSignal ?signalType))
#  (Values ?signalType sigHalt)
#  (Pre p1 TrainAt(?train ?currentSignal))
#  (Pre p2 SignalAt(?currentSignal ?l1 ?l2))
#  (Pre p3 SignalAt(?nextSignal ?l2 ?l2)) # Halt signals have start & end at same place
#  (Add e1 TrainAt(?train ?nextSignal))
#  (Constraint Duration[4000,INF](task)) # Longer because train stops
#  (Del p1)
#)

## Actual driving

(:method # already there
  (Head drive(?train ?goalSignal))
  (Pre p1 TrainAt(?train ?goalSignal))
  (Constraint During(task,p1))
  (Constraint Duration[10,INF](task))
)

(:method # still has to drive
  (Head drive(?train ?goalSignal))
  (Pre p1 TrainAt(?train ?currentSignal))
  (VarDifferent ?currentSignal ?goalSignal)

  # simple test to assure that nextSignal is of type signal
#  (Pre p2 Type(?goalSignal ?type))
#  (Values ?type entry)

#  (Sub s0 request_signal(?train ?currentSignal))
#  (Sub s1 request_signal(?train ?nextSignal))
  (Sub s2 drive_segment(?train ?currentSignal ?nextSignal))
#  (VarDifferent ?currentSignal ?nextSignal)
#  (Sub s3 !free_signal(?train ?currentSignal))
  (Sub s4 drive(?train ?goalSignal))
  
#  (Ordering s0 s2)
#  (Ordering s1 s2)
#  (Ordering s2 s3)
  (Ordering s2 s4)

  (Constraint Starts(s2,task))
  (Constraint Before(s2,s4))
# (Constraint Before[1,1000](s2,s3))
)


(:operator 
  (Head !drive_to_next_signal(?train ?nextSignal))
  (Add e0 TrainAt(?train ?nextSignal))
  (Constraint Duration[500,INF](task))
)

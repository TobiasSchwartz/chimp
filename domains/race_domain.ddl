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

(HybridHTNDomain RACEDomain)

(MaxArgs 5)


(Resource navigationCapacity 1)
##
(Resource leftArm1 1)
(Resource rightArm1 1)
(Resource leftArm1ManCapacity 1)
(Resource rightArm1ManCapacity 1)

(StateVariable RobotAt 2 n)
(StateVariable HasArmPosture 1 leftArm1 rightArm1)
##
(StateVariable On 1 mug1 mug2 mug3)


################################
####  OPERATORS ################

# MOVE_BASE
(:operator
 (Head !move_base(?toArea))
 (Pre p1 RobotAt(?fromArea))
 (Constraint OverlappedBy(task,p1))
# (Constraint Duration[5,INF](task))
 (Add e1 RobotAt(?toArea))
# (Constraint Overlaps(task,e1)) # not needed
 (Del p1)
 (ResourceUsage 
  (Usage navigationCapacity 1))
 
 #(Add e7 RobotAt(preManipulationAreaWestTable2))
 #(Constraint OverlappedBy(task,e7))
)

# MOVE_BASE_BLIND   PreArea to ManArea
(:operator
 (Head !move_base_blind(?mArea))
 (Pre p1 RobotAt(?preArea))       # TODO use type restriction
 (Pre p2 Connected(?plArea ?mArea ?preArea))
 (Constraint OverlappedBy(task,p1))
 (Constraint Duration[10,10](task))
 (Add e1 RobotAt(?mArea))
 (Constraint Overlaps(task,e1))
 (Del p1)
 (ResourceUsage 
    (Usage navigationCapacity 1))
)

# MOVE_BASE_BLIND   ManArea to PreArea
(:operator
 (Head !move_base_blind(?preArea))
 (Pre p1 RobotAt(?mArea))       # TODO use type restriction
 (Pre p2 Connected(?plArea ?mArea ?preArea))
 (Constraint OverlappedBy(task,p1))
 (Constraint Duration[3,10](task))
 (Add e1 RobotAt(?preArea))
 (Constraint Overlaps(task,e1))
 (Del p1)
 (ResourceUsage 
    (Usage navigationCapacity 1))
)

# TUCK_ARMS
(:operator
 (Head !tuck_arms(?leftGoal ?rightGoal))
 (Pre p1 HasArmPosture(?leftArm ?oldLeft))
 (Pre p2 HasArmPosture(?rightArm ?oldRight))
 (Del p1)
 (Del p2)
 (Add e1 HasArmPosture(?leftArm ?leftGoal))
 (Add e2 HasArmPosture(?rightArm ?rightGoal))
# (Type ?oldLeft ArmPosture)
 (Values ?leftArm leftArm1)
 (Values ?rightArm rightArm1)
 (Values ?leftGoal ArmTuckedPosture ArmUnTuckedPosture)
 (Values ?rightGoal ArmTuckedPosture ArmUnTuckedPosture)

 (ResourceUsage 
    (Usage leftArm1ManCapacity 1))
 (ResourceUsage 
    (Usage rightArm1ManCapacity 1))
 (Constraint Duration[5,5](task))
# (Constraint Duration[1,10000](e1))
# (Constraint Duration[1,10000](e2))
)

# MOVE_TORSO
(:operator
 (Head !move_torso(?newPosture))
 (Pre p1 HasTorsoPosture(?oldPosture))
 (Constraint OverlappedBy(task,p1))
 (Del p1)
 (Add e1 HasTorsoPosture(?newPosture))
 (Constraint Duration[5,5](task))
)

# PICK_UP_OBJECT
(:operator
 (Head !pick_up_object(?obj ?arm))
 (Pre p1 On(?obj ?fromArea))
 (Pre p2 RobotAt(?mArea))
 (Pre p3 Connected(?fromArea ?mArea ?preArea))
 (Pre p4 Holding(?arm ?nothing))
 (Values ?nothing nothing)
 (Del p1)
 (Del p4)
 (Add e1 Holding(?arm ?obj))

 (Constraint OverlappedBy(task,p1))
 (Constraint During(task,p2)) # robot has to be at the table the wohle time
 (Constraint During(task,p3))
 (Constraint OverlappedBy(task,p4))
 (Constraint Meets(p4,e1))
 # TODO Which constraint for effect? 
 (Constraint Duration[5,5](task))
 
 (ResourceUsage 
    (Usage leftArm1ManCapacity 1)
    (Param 2 leftArm1))
 (ResourceUsage 
    (Usage rightArm1ManCapacity 1)
    (Param 2 rightArm1))
)

# PLACE_OBJECT
(:operator
 (Head !place_object(?obj ?arm ?plArea))

 (Pre p1 Holding(?arm ?obj))
 (Pre p2 RobotAt(?mArea))
 (Pre p3 Connected(?plArea ?mArea ?preArea))
 (Pre p4 HasArmPosture(?arm ?armPosture)) # TODO maybe not necessary
 (Values ?armPosture ArmToSidePosture)
# (Pre p5 HasTorsoPosture(?torsoPosture)) # not necessary
# (Values ?torsoPosture TorsoUpPosture)
 (Del p1)
(Add e1 Holding(?arm ?nothing))
(Values ?nothing nothing)
 (Add e2 On(?obj ?plArea))

 (Constraint OverlappedBy(task,p1))
 (Constraint During(task,p2)) # robot has to be at the table the wohle time
 (Constraint During(task,p3))
 (Constraint Meets(p1,e1))
 # TODO Which constraint for effect? 
 (Constraint Duration[5,5](task))
 
 (ResourceUsage 
    (Usage leftArm1ManCapacity 1)
    (Param 2 leftArm1))
 (ResourceUsage 
    (Usage rightArm1ManCapacity 1)
    (Param 2 rightArm1))
 )

# MOVE_ARM_TO_SIDE
(:operator
 (Head !move_arm_to_side(?arm))
 (Pre p1 HasArmPosture(?arm ?oldPosture))
 (Del p1)
 (Add e1 HasArmPosture(?arm ?newPosture))

 (Values ?oldPosture ArmUnTuckedPosture ArmCarryPosture ArmUnnamedPosture ArmToSidePosture)
 (Values ?newPosture ArmToSidePosture)

 (ResourceUsage 
    (Usage leftArm1ManCapacity 1)
    (Param 1 leftArm1))
 (ResourceUsage 
    (Usage rightArm1ManCapacity 1)
    (Param 1 rightArm1))
 
 (Constraint Duration[5,5](task))
 (Constraint OverlappedBy(task,p1))
 (Constraint Overlaps(task,e1))
)

# MOVE_ARMS_TO_CARRYPOSTURE
(:operator
 (Head !move_arms_to_carryposture())
 (Pre p1 HasArmPosture(?leftArm ?oldLeft))
 (Pre p2 HasArmPosture(?rightArm ?oldRight))
 (Pre p3 HasTorsoPosture(?torsoPosture))
 (Del p1)
 (Del p2)
 (Add e1 HasArmPosture(?leftArm ?newPosture))
 (Add e2 HasArmPosture(?rightArm ?newPosture))
# (Type ?oldLeft ArmPosture)
 (Values ?leftArm leftArm1)
 (Values ?rightArm rightArm1)
 (Values ?newPosture ArmCarryPosture)
 (Values ?rightGoal ArmTuckedPosture ArmUnTuckedPosture)
 (Values ?torsoPosture TorsoUpPosture TorsoMiddlePosture)

 (ResourceUsage 
    (Usage leftArm1ManCapacity 1))
 (ResourceUsage 
    (Usage rightArm1ManCapacity 1))
 (Constraint Duration[5,5](task))
 (Constraint OverlappedBy(task,p1))
 (Constraint OverlappedBy(task,p2))
 (Constraint Overlaps(task,e1))   # TODO is this correct?
 (Constraint Overlaps(task,e2))
 )

# OBSERVE_OBJECTS_ON_AREA
(:operator
 (Head !observe_objects_on_area(?plArea))
 (Pre p1 RobotAt(?robotArea))    
 (Pre p2 Connected(?plArea ?robotArea ?preArea))
 (Constraint During(task,p1))
 (Constraint During(task,p2))
 (Constraint Duration[5,5](task))
)


################################

(FluentResourceUsage 
  (Usage leftArm1 1) 
  (Fluent Holding)
  (Param 2 leftArm1)
)

(FluentResourceUsage 
  (Usage rightArm1 1) 
  (Fluent Holding)
  (Param 2 rightArm1)
)

#################################

(:method
 (Head adapt_torso(?newPose))
 (Pre p1 HasTorsoPosture(?oldPose))
 (VarDifferent ?newPose ?oldPose) 
 (Constraint Duration[3,10](task))
 (Sub s1 !move_torso(?newPose))
 (Constraint Equals(s1,task))
 )


(:method
 (Head adapt_torso(?posture))
 (Pre p1 HasTorsoPosture(?posture))
 (Constraint Duration[0,0](task))
 (Constraint During(task,p1))
 )

###

(:method   # holding nothing
 (Head torso_assume_driving_pose())
  (Pre p1 Holding(?leftArm ?nothing))
  (Pre p2 Holding(?rightArm ?nothing))
  (Values ?nothing nothing)
  (Values ?leftArm leftArm1)
  (Values ?rightArm rightArm1)
# (Constraint Duration[3,10](task))
  (Sub s1 adapt_torso(?newPose))
  (Values ?newPose TorsoDownPosture)
  (Constraint Equals(s1,task))
)

(:method # holding something
 (Head torso_assume_driving_pose())
  (Pre p1 Holding(?arm ?obj))
  (NotValues ?obj nothing)
#  (Type ?obj Object)
# (Constraint Duration[3,10](task))
  (Sub s1 adapt_torso(?newPose))
  (Values ?newPose TorsoMiddlePosture)
  (Constraint Equals(s1,task))
)

# TODO Version for tray


###

(:method  # Arms already there. Nothing to do.
 (Head adapt_arms(?posture))
 (Pre p1 HasArmPosture(?leftArm ?posture))
 (Pre p2 HasArmPosture(?rightArm ?posture))

 (Values ?leftArm leftArm1)
 (Values ?rightArm rightArm1)
 
 (Constraint Duration[0,0](task))
 (Constraint During(task,p1))
 (Constraint During(task,p2))
 )

(:method  # tuck arms
 (Head adapt_arms(?posture))
 (Pre p1 HasArmPosture(?arm ?currentposture))

 (Values ?posture ArmTuckedPosture)
 (NotValues ?currentposture ArmTuckedPosture)
 
 (Constraint Duration[3,10](task))

 (Sub s1 !tuck_arms(?posture ?posture))
 (Constraint Equals(s1,task))
)

(:method  # to carryposture
 (Head adapt_arms(?posture))
 (Pre p1 HasArmPosture(?arm ?currentposture))

 (Values ?posture ArmCarryPosture)
 (NotValues ?currentposture ArmCarryPosture)
 
 (Constraint Duration[3,10](task))

 (Sub s1 !move_arms_to_carryposture())
 (Constraint Equals(s1,task))
 )

###

(:method    # holding nothing
 (Head arms_assume_driving_pose())
  (Pre p1 Holding(?leftArm ?nothing))
  (Pre p2 Holding(?rightArm ?nothing))
  (Values ?nothing nothing)
  (Values ?leftArm leftArm1)
  (Values ?rightArm rightArm1)

  (Sub s1 adapt_arms(?newPose)) 
  (Values ?newPose ArmTuckedPosture)
  (Constraint Equals(s1,task))
)

(:method    # holding something
 (Head arms_assume_driving_pose())
  (Pre p1 Holding(?arm ?obj))
  (NotValues ?obj nothing)
#  (Type ?obj Object)
# (Constraint Duration[3,10](task))
  (Sub s1 adapt_arms(?newPose))
  (Values ?newPose ArmCarryPosture)
  (Constraint Equals(s1,task))
)  # todo check nothing on tray


###

(:method    # already there
 (Head drive_robot(?toArea))
  (Pre p1 RobotAt(?toArea))
  (Constraint During(task,p1))
  (Constraint Duration[0,0](task))
 )

(:method    # not at manipulationarea
 (Head drive_robot(?toArea))

 (Pre p1 RobotAt(?fromArea))
 (VarDifferent ?toArea ?fromArea)

 (NotValues ?fromArea manipulationAreaEastCounter1 manipulationAreaNorthTable1) # TODO: USE TYPE!!!
  
# (Constraint Duration[20,30](task))
 (Sub s1 torso_assume_driving_pose())
 # (Constraint During(s1,task))
 (Sub s2 arms_assume_driving_pose())

 (Sub s3 !move_base(?toArea))
 (Ordering s1 s3)
 (Ordering s2 s3)
 )

(:method    # at manipulationarea
 (Head drive_robot(?toArea))

 (Pre p1 RobotAt(?fromArea))
 (VarDifferent ?toArea ?fromArea)

 (Values ?fromArea manipulationAreaEastCounter1 manipulationAreaNorthTable1) # TODO: USE TYPE!!!
  
 # (Constraint Duration[20,30](task))

 (Pre p2 Connected(?plArea ?fromArea ?preArea))

 (Sub s0 !move_base_blind(?preArea))
   
 (Sub s1 torso_assume_driving_pose())
 # (Constraint During(s1,task))
 (Sub s2 arms_assume_driving_pose())

 (Sub s3 !move_base(?toArea))
 (Ordering s0 s1)
 (Ordering s0 s2)
 (Ordering s0 s3)
 (Ordering s1 s3)
 (Ordering s2 s3)
)

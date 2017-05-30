from z3 import *
import time

s = Solver()

# types: quote and union
Subscriber = Datatype('Subscriber') #token: assume two tokens "s1" and "s2", therefore, size of Subscriber=2
Subscriber.declare('s1')
Subscriber.declare('s2')
Subscriber.declare('s3')
Subscriber.declare('s4')
Subscriber.declare('s5')
Subscriber = Subscriber.create()

Initiator = Datatype('Initiator')
Initiator.declare('AI')
Initiator.declare('WI')
Initiator.declare('SI')
Initiator = Initiator.create()

Recipient = Datatype('Recipient')
Recipient.declare('WR')
Recipient.declare('SR')
Recipient = Recipient.create()

Status = Datatype('Status')
Status.declare('fr')
Status.declare('un')
Status.declare('INITIATOR', ('get_initiator', Initiator)) # the way to assign union
Status.declare('RECIPIENT', ('get_recipient', Recipient))
Status = Status.create()

# lift (for partial function)
Subscriber_lift = Datatype('Subscriber_lift')
Subscriber_lift.declare('SUBSCRIBER', ('get_subscriber', Subscriber))
Subscriber_lift.declare('NDF')
Subscriber_lift = Subscriber_lift.create()

Status_lift = Datatype('Status_lift')
Status_lift.declare('STATUS', ('get_status', Status))
Status_lift.declare('NDF')
Status_lift = Status_lift.create()

# State: Exchange: mk_Exchange(status,calls)
# Define maps using uninterpreted functions
status = Function('status',Subscriber,Status_lift)
calls = Function('calls',Subscriber,Subscriber_lift)

i = Const('i',Subscriber) # for ForAll/Exists
#j = Const('j',Subscriber) # for ForAll/Exists

# State invariant
# 2017/3/1 :
#   According to the paper (fme971.pdf), PO shall reveal all necessary context (related segments of the VDM-SL model)
#   Therefore, we shall not include the state invariant implicitly.
# 2017/3/7 :
#   After examined the book "Systemic Software Development Using VDM" with composite datatype and states,
#   invariants are implicitly included in the context information of the proof obligation.
"""
# invariant template
s.add(
  ForAll(i,
    Implies(
	  calls(i)!=Subscriber_lift.NDF,
	  Or(
        And(
		  status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
		  calls(i)!=Subscriber_lift.NDF,
	      status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR))
		),
        And(
		  status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)),
		  calls(i)!=Subscriber_lift.NDF,
		  status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.SR))
		)
	  )
	)
  )
)
"""
k  = Const('k',Subscriber)
l  = Const('l',Subscriber)
s.add( # constraint of inmap (calls: inmap Subscriber to Subscriber)
  ForAll([k,l],
    If(
      k==l,
	  calls(k)==calls(l),
	  Or(
	    And(
	      calls(k)==Subscriber_lift.NDF,
	      calls(l)==Subscriber_lift.NDF
		),
		calls(k)!=calls(l)
	  )
	)
  )
)

#Proof Obligation 1: (With Negation)
#status, status~, calls, calls~, Exchange, Exchange~: legal map application obligation @ in 'EXCH' (telephone.vdmsl) at line 17:9
#(forall mk_Exchange(status, calls):EXCH`Exchange & (forall i in set (dom calls) & (i in set (dom status))))
#
# The PO is in the form:
#    forall[status,calls]. inv_Exchange(status,calls) => forall[i]. (P)
# where P is a boolean formula
# The negation of the PO then is in the form:
#    Exists[status,calls]. ( inv_Exchange(status,calls) and Not( forall[i]. (P) ) )
# The above foram can be used for PO1~PO6
print "\n*** Telephone: proof obligation 1 ***\n"
start_time = time.clock()
s.push()
s.add(
  And(
    ForAll(i, # inv_Exchange
      Implies(
	    calls(i)!=Subscriber_lift.NDF,
	    Or(
          And(
		    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
		    calls(i)!=Subscriber_lift.NDF,
	        status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR))
		  ),
          And(
		    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)),
		    calls(i)!=Subscriber_lift.NDF,
		    status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.SR))
		  )
	    )
	  )
    ),
    Not(
	  ForAll(i,
        Implies(calls(i)!=Subscriber_lift.NDF, status(i)!=Status_lift.NDF)
	  )
    )
  )
)

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 2: (With Negation)
#status, status~, calls, calls~, Exchange, Exchange~: legal map application obligation @ in 'EXCH' (telephone.vdmsl) at line 17:30
#(forall mk_Exchange(status, calls):EXCH`Exchange & (forall i in set (dom calls) & ((status(i) = <WI>) => (calls(i) in set (dom status)))))
print "\n*** Telephone: proof obligation 2 ***\n"
start_time = time.clock()
s.push()
s.add(
  And(
    ForAll(i, # inv_Exchange
      Implies(
	    calls(i)!=Subscriber_lift.NDF,
	    Or(
          And(
		    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
		    calls(i)!=Subscriber_lift.NDF,
	        status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR))
		  ),
          And(
		    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)),
		    calls(i)!=Subscriber_lift.NDF,
		    status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.SR))
		  )
	    )
	  )
    ),
    Not(
	  ForAll(i,
        Implies(
          calls(i)!=Subscriber_lift.NDF,
	      Implies(
	        status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
	        status(Subscriber_lift.get_subscriber(calls(i)))!=Status_lift.NDF)
	      )
      )
    )
  )
)

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 3: (With Negation)
#status, status~, calls, calls~, Exchange, Exchange~: legal map application obligation @ in 'EXCH' (telephone.vdmsl) at line 17:37
#(forall mk_Exchange(status, calls):EXCH`Exchange & (forall i in set (dom calls) & ((status(i) = <WI>) => (i in set (dom calls)))))
print "\n*** Telephone: proof obligation 3 ***\n"
start_time = time.clock()
s.push()
s.add(
  And(
    ForAll(i, # inv_Exchange
      Implies(
	    calls(i)!=Subscriber_lift.NDF,
	    Or(
          And(
		    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
		    calls(i)!=Subscriber_lift.NDF,
	        status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR))
		  ),
          And(
		    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)),
		    calls(i)!=Subscriber_lift.NDF,
		    status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.SR))
		  )
	    )
	  )
    ),
    Not(
	  ForAll(i,
        Implies(
          calls(i)!=Subscriber_lift.NDF,
	      Implies(
		    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
		    calls(i)!=Subscriber_lift.NDF)
	    )
      )
	)
  )
)

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 4: (With Negation)
#status, status~, calls, calls~, Exchange, Exchange~: legal map application obligation @ in 'EXCH' (telephone.vdmsl) at line 19:9
#(forall mk_Exchange(status, calls):EXCH`Exchange & (forall i in set (dom calls) & ((not ((status(i) = <WI>) and (status(calls(i)) = <WR>))) => (i in set (dom status)))))
print "\n*** Telephone: proof obligation 4 ***\n"
start_time = time.clock()
s.push()
s.add(
  And(
    ForAll(i, # inv_Exchange
      Implies(
	    calls(i)!=Subscriber_lift.NDF,
	    Or(
          And(
		    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
		    calls(i)!=Subscriber_lift.NDF,
	        status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR))
		  ),
          And(
		    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)),
		    calls(i)!=Subscriber_lift.NDF,
		    status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.SR))
		  )
	    )
	  )
    ),
    Not(
	  ForAll(i,
        Implies(
	      calls(i)!=Subscriber_lift.NDF,
	      Implies(
		    Not(
			  And(
			    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
			    status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR))
			  )
			),
		    status(i)!=Status_lift.NDF
		  )
	    )
      )
	)
  )
)

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 5: (With Negation)
#status, status~, calls, calls~, Exchange, Exchange~: legal map application obligation @ in 'EXCH' (telephone.vdmsl) at line 19:30
#(forall mk_Exchange(status, calls):EXCH`Exchange & (forall i in set (dom calls) & ((not ((status(i) = <WI>) and (status(calls(i)) = <WR>))) => ((status(i) = <SI>) => (calls(i) in set (dom status))))))
print "\n*** Telephone: proof obligation 5 ***\n"
start_time = time.clock()
s.push()
s.add(
  And(
    ForAll(i, # inv_Exchange
      Implies(
	    calls(i)!=Subscriber_lift.NDF,
	    Or(
          And(
		    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
		    calls(i)!=Subscriber_lift.NDF,
	        status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR))
		  ),
          And(
		    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)),
		    calls(i)!=Subscriber_lift.NDF,
		    status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.SR))
		  )
	    )
	  )
    ),
    Not(
	  ForAll(i,
        Implies(
	      calls(i)!=Subscriber_lift.NDF,
	      Implies(
		    Not(
			   And(
			      status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
			      status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR))
			   )
			),
			Implies(
			   status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)),
			   status(Subscriber_lift.get_subscriber(calls(i)))!=Status_lift.NDF
			)
		  )
        )
      )
	)
  )
)

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 6: (With Negation)
#status, status~, calls, calls~, Exchange, Exchange~: legal map application obligation @ in 'EXCH' (telephone.vdmsl) at line 19:37
#(forall mk_Exchange(status, calls):EXCH`Exchange & (forall i in set (dom calls) & ((not ((status(i) = <WI>) and (status(calls(i)) = <WR>))) => ((status(i) = <SI>) => (i in set (dom calls))))))
print "\n*** Telephone: proof obligation 6 ***\n"
start_time = time.clock()
s.push()
k  = Const('k',Subscriber)
l  = Const('l',Subscriber)
s.add(
  And(
    ForAll(i, # inv_Exchange
      Implies(
	    calls(i)!=Subscriber_lift.NDF,
	    Or(
          And(
		    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
		    calls(i)!=Subscriber_lift.NDF,
	        status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR))
		  ),
          And(
		    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)),
		    calls(i)!=Subscriber_lift.NDF,
		    status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.SR))
		  )
	    )
	  )
    ),
    Not(
	  ForAll(i,
        Implies(
	      calls(i)!=Subscriber_lift.NDF,
	      Implies(
		    Not(
		      And(
		        status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
		        status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR))
		      )
		    ),
		    Implies(
		      status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)),
		      calls(i)!=Subscriber_lift.NDF
		    )
		  )
	    )
	  )
    )
  )
)

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 7: ("Without" Negation)
#status, status~, calls, calls~, Exchange, Exchange~: state invariant satisfiable obligation @ in 'EXCH' (telephone.vdmsl) at line 12:8
#(exists status:map (Subscriber) to (Status), calls:inmap (Subscriber) to (Subscriber) & (forall i in set (dom calls) & (((status(i) = <WI>) and (status(calls(i)) = <WR>)) or ((status(i) = <SI>) and (status(calls(i)) = <SR>)))))
print "\n*** Telephone: proof obligation 7 ***\n"
start_time = time.clock()
s.push()
s.add( # constraint of inmap (calls: inmap Subscriber to Subscriber)
  ForAll([k,l],
    If(
      k==l,
	  calls(k)==calls(l),
	  Or(
	    And(
	      calls(k)==Subscriber_lift.NDF,
	      calls(l)==Subscriber_lift.NDF
		),
		calls(k)!=calls(l)
	  )
	)
  )
)
s.add(
  ForAll(i,
    Implies(
	  calls(i)!=Subscriber_lift.NDF,
	  Or(
        And(
		  status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
		  calls(i)!=Subscriber_lift.NDF,
	      status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR))
		),
        And(
		  status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)),
		  calls(i)!=Subscriber_lift.NDF,
		  status(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.RECIPIENT(Recipient.SR))
		)
	  )
	)
  )
)
# test for non-empty mappings
#s.add(calls(Subscriber.s1)==Subscriber_lift.SUBSCRIBER(Subscriber.s2))

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))

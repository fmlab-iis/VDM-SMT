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
# try defin maps using uninterpreted functions
status = Function('status',Subscriber,Status_lift)
calls = Function('calls',Subscriber,Subscriber_lift)

i = Const('i',Subscriber) # for ForAll/Exists

# State invariant template
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

#Proof Obligation 12: (With Negation)
#Answer: legal map application obligation @ in 'EXCH' (telephone.vdmsl) at line 50:42
#((r in set (dom (status :> {<WR>}))) => (r in set (dom (inverse calls))))
"""
The proof obligation is in the form:
  ForAll[r,status,calls] (P -> Q)
After negated, the obligation becomes the form:
  Exists[r,status,calls] (P and Not(Q))
Where,
  P: (r in set (dom (status :> {<WR>})))
  Q: (r in set (dom (inverse calls)))
We will use i declared before as r
"""
print "\nTelephone: proof obligation 12"
start_time = time.clock()
s.push()
r  = Const('r',Subscriber)

# constraint of inmap (calls: inmap Subscriber to Subscriber)
k = Const('k',Subscriber)
l = Const('l',Subscriber)
s.add( 
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
"""
# Cnstraint of calls : if a subscriber is defined in domain of calls, the range cannot be itself
# Note: This constraint is missed in the specification.
s.add( 
  ForAll(k,
    Implies(
	  calls(k)!=Subscriber_lift.NDF,
	  Subscriber_lift.get_subscriber(calls(k))!=k
	)
  )
)
"""
s.add(
  And(
    status(r)==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR)), #P
    Not(
	  And( #Q
	    Subscriber_lift.is_SUBSCRIBER(calls(i)),
	    Subscriber_lift.get_subscriber(calls(i))==r
	  )
	)
  )
)
#s.add(calls(Subscriber.s1)!=Subscriber_lift.NDF)
#s.add(calls(Subscriber.s1)==Subscriber_lift.SUBSCRIBER(Subscriber.s2))
print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 17: (With Negation)
#ClearWait: legal map application obligation @ in 'EXCH' (telephone.vdmsl) at line 61:41
#((i in set (dom (status :> {<WI>}))) => (i in set (dom calls)))
"""
The proof obligation is in the form:
  ForAll[r,status,calls] (P -> Q)
After negated, the obligation becomes the form:
  Exists[r,status,calls] (P and Not(Q))
Where,
  P: (i in set (dom (status :> {<WI>})))
  Q: (i in set (dom calls))
We will use i declared before as r
"""
print "\nTelephone: proof obligation 17"
start_time = time.clock()
s.push()

# constraint of inmap (calls: inmap Subscriber to Subscriber)
k = Const('k',Subscriber)
l = Const('l',Subscriber)
s.add( 
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
  And(
    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)), #P
    Not(
	  calls(i)!=Subscriber_lift.NDF #Q
	)
  )
)

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 20: (With Negation)
#ClearSpeak: legal map application obligation @ in 'EXCH' (telephone.vdmsl) at line 68:41
#((i in set (dom (status :> {<SI>}))) => (i in set (dom calls)))
"""
The proof obligation is in the form:
  ForAll[r,status,calls] (P -> Q)
After negated, the obligation becomes the form:
  Exists[r,status,calls] (P and Not(Q))
Where,
  P: (i in set (dom (status :> {<SI>})))
  Q: (i in set (dom calls))
We will use i declared before as r
"""
print "\nTelephone: proof obligation 20"
start_time = time.clock()
s.push()

# constraint of inmap (calls: inmap Subscriber to Subscriber)
k = Const('k',Subscriber)
l = Const('l',Subscriber)
s.add( 
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
  And(
    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)), #P
    Not(
	  calls(i)!=Subscriber_lift.NDF #Q
	)
  )
)
#s.add(calls(Subscriber.s1)!=Subscriber_lift.NDF)
#s.add(calls(Subscriber.s1)==Subscriber_lift.SUBSCRIBER(Subscriber.s2))
print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 23: (With Negation)
#Suspend: legal map application obligation @ in 'EXCH' (telephone.vdmsl) at line 75:42
#((r in set (dom (status :> {<SR>}))) => (r in set (dom (inverse calls))))
"""
The proof obligation is in the form:
  ForAll[r,status,calls] (P -> Q)
After negated, the obligation becomes the form:
  Exists[r,status,calls] (P and Not(Q))
Where,
  P: (r in set (dom (status :> {<SR>})))
  Q: (r in set (dom (inverse calls)))
We will use i declared before as r
"""
print "\nTelephone: proof obligation 23"
start_time = time.clock()
s.push()
r  = Const('r',Subscriber)

# constraint of inmap (calls: inmap Subscriber to Subscriber)
k = Const('k',Subscriber)
l = Const('l',Subscriber)
s.add( 
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
  And(
    status(r)==Status_lift.STATUS(Status.RECIPIENT(Recipient.SR)), #P
    Not(
	  And( #Q
	    Subscriber_lift.is_SUBSCRIBER(calls(i)),
	    Subscriber_lift.get_subscriber(calls(i))==r
	  )
	)
  )
)
#s.add(calls(Subscriber.s1)!=Subscriber_lift.NDF)
#s.add(calls(Subscriber.s1)==Subscriber_lift.SUBSCRIBER(Subscriber.s2))
print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))

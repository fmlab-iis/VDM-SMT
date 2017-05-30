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

"""
# state invariant template
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

#Proof Obligation 9: (With Negation)
#Connect: enumeration map injectivity obligation @ in 'EXCH' (telephone.vdmsl) at line 38:28
#(((i in set (dom (status :> {<AI>}))) and (r in set (dom (status :> {<fr>})))) => (forall m1, m2 in set {{i |-> <WI>}, {r |-> <WR>}} & (forall d3 in set (dom m1), d4 in set (dom m2) & ((d3 = d4) => (m1(d3) = m2(d4))))))
"""
The proof obligation is the form:
  ForAll[i,r,status,calls] (P -> ForAll[m1,m2] (Q -> ForAll[d3,d4] (R -> S) ) )
After negated, the obligation becomes the form:
  Exists[i,r,status,calls] (P and Exists[m1,m2] (Q and Exists[d3,d4] (R and Not(S)) ) )  
Where,
  P: (i in set (dom (status :> {<AI>}))) and (r in set (dom (status :> {<fr>})))
  Q: m1, m2 in set {{i |-> <WI>}, {r |-> <WR>}}
  R: d3 in set (dom m1), d4 in set (dom m2)
  S: (d3 = d4) => (m1(d3) = m2(d4))
"""
print "\nTelephone: proof obligation 9"
start_time = time.clock()
s.push()
r  = Const('r',Subscriber)
m1 = Function('m1',Subscriber,Status_lift)
m2 = Function('m2',Subscriber,Status_lift)
d3 = Const('d3',Subscriber)
d4 = Const('d4',Subscriber)

k  = Const('k',Subscriber)
s.add(
  And(
    And( #P
      status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.AI)),
	  status(r)==Status_lift.STATUS(Status.fr)
	),
	And(
	  And( #Q
		Xor(
		  And(
		    m1(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
			ForAll(k, Implies(k!=i, m1(k)==Status_lift.NDF) )
		  ),
		  And(
		    m1(r)==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR)),
			ForAll(k, Implies(k!=r, m1(k)==Status_lift.NDF) )
		  )
		),
		Xor(
		  And(
			m2(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
			ForAll(k, Implies(k!=i, m2(k)==Status_lift.NDF) )
		  ),
		  And(
			m2(r)==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR)),
			ForAll(k, Implies(k!=i, m2(k)==Status_lift.NDF) )
		  )
		)
	  ),
	  And(
	    And( #R
	      m1(d3)!=Status_lift.NDF,
		  m2(d4)!=Status_lift.NDF
	    ),
	    And( #S
	      d3==d4,
		  m1(d3)!=m2(d4)
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


#Proof Obligation 14: (With Negation)
#Answer: enumeration map injectivity obligation @ in 'EXCH' (telephone.vdmsl) at line 50:28
#((r in set (dom (status :> {<WR>}))) => (forall m1, m2 in set {{r |-> <SR>}, {(inverse calls)(r) |-> <SI>}} & (forall d3 in set (dom m1), d4 in set (dom m2) & ((d3 = d4) => (m1(d3) = m2(d4))))))
"""
The proof obligation is the form:
  ForAll[i,r,status,calls] (P -> ForAll[m1,m2] (Q -> ForAll[d3,d4] (R -> S) ) )
After negated, the obligation becomes the form:
  Exists[i,r,status,calls] (P and Exists[m1,m2] (Q and Exists[d3,d4] (R and Not(S)) ) )  
Where,
  P: (r in set (dom (status :> {<WR>})))
  Q: m1, m2 in set {{r |-> <SR>}, {(inverse calls)(r) |-> <SI>}}
  R: d3 in set (dom m1), d4 in set (dom m2)
  S: (d3 = d4) => (m1(d3) = m2(d4))
"""
print "\nTelephone: proof obligation 14"
start_time = time.clock()
s.push()
r  = Const('r',Subscriber)
j  = Const('j',Subscriber)
m1 = Function('m1',Subscriber,Status_lift)
m2 = Function('m2',Subscriber,Status_lift)
d3 = Const('d3',Subscriber)
d4 = Const('d4',Subscriber)

k  = Const('k',Subscriber)
l  = Const('l',Subscriber)

# constraint of inversible map (calls) : s1==s2 -> calls(s1)==calls(s2), s1!=s2 -> calls(s1)!=calls(s2) or (calls(s1)==calls(s2)==NDF)
# if seems this is not sufficient, becaue Z3 give a model with a subscriber calls to itself
# this is not OK for a telephone exchange system, while is OK for a inmap
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
    status(r)==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR)), # P
	And(
	  And( #Q
		Xor(
		  And(
		    m1(r)==Status_lift.STATUS(Status.RECIPIENT(Recipient.SR)),
			ForAll(k, Implies(k!=r, m1(k)==Status_lift.NDF) )
		  ),
		  And(
		    calls(i)!=Subscriber_lift.NDF, # inverse map is not empty
		    Subscriber_lift.get_subscriber(calls(i)) == r, # inverse_calls(r) == i
			#i!=r,
		    m1(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)),
			ForAll(k, Implies(k!=i, m1(k)==Status_lift.NDF) )
		  )
		),
		Xor(
		  And(
		    m2(r)==Status_lift.STATUS(Status.RECIPIENT(Recipient.SR)),
			ForAll(k, Implies(k!=r, m2(k)==Status_lift.NDF) )
		  ),
		  And(
		    calls(j)!=Subscriber_lift.NDF, # inverse map is not empty
		    Subscriber_lift.get_subscriber(calls(j)) == r, # inverse_calls(r) == j
			#j!=r,
		    m2(j)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)),
			ForAll(k, Implies(k!=j, m2(k)==Status_lift.NDF) )
		  )
		)
	  ),
	  And(
	    And( #R
	      m1(d3)!=Status_lift.NDF,
		  m2(d4)!=Status_lift.NDF
	    ),
	    And( #S
	      d3==d4,
		  m1(d3)!=m2(d4)
	    )
	  )
	)
  )
)
#s.add(calls(Subscriber.s1)==Subscriber_lift.SUBSCRIBER(Subscriber.s2))

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 18: (With Negation)
#ClearWait: enumeration map injectivity obligation @ in 'EXCH' (telephone.vdmsl) at line 61:28
#((i in set (dom (status :> {<WI>}))) => (forall m1, m2 in set {{i |-> <fr>}, {calls(i) |-> <fr>}} & (forall d3 in set (dom m1), d4 in set (dom m2) & ((d3 = d4) => (m1(d3) = m2(d4))))))
"""
The proof obligation is the form:
  ForAll[i,r,status,calls] (P -> ForAll[m1,m2] (Q -> ForAll[d3,d4] (R -> S) ) )
After negated, the obligation becomes the form:
  Exists[i,r,status,calls] (P and Exists[m1,m2] (Q and Exists[d3,d4] (R and Not(S)) ) )  
Where,
  P: (i in set (dom (status :> {<WI>})))
  Q: m1, m2 in set {{i |-> <fr>}, {calls(i) |-> <fr>}}
  R: d3 in set (dom m1), d4 in set (dom m2)
  S: (d3 = d4) => (m1(d3) = m2(d4))
"""
print "\nTelephone: proof obligation 18"
start_time = time.clock()
s.push()
#r  = Const('r',Subscriber)
m1 = Function('m1',Subscriber,Status_lift)
m2 = Function('m2',Subscriber,Status_lift)
d3 = Const('d3',Subscriber)
d4 = Const('d4',Subscriber)

k  = Const('k',Subscriber)

s.add( # constraint of inversible map (calls) : if a subscriber is defined in domain of calls, the range cannot be itself
  ForAll(k,
    Implies(
	  calls(k)!=Subscriber_lift.NDF,
	  Subscriber_lift.get_subscriber(calls(k))!=k
	)
  )
)

s.add(
  And(
    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)), #P
	And(
	  And( #Q
		Xor(
		  And(
		    m1(i)==Status_lift.STATUS(Status.fr),
			ForAll(k, Implies(k!=i, m1(k)==Status_lift.NDF) )
		  ),
		  And(
		    Subscriber_lift.is_SUBSCRIBER(calls(i)),
		    m1(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.fr),
			ForAll(k, Implies(k!=r, m1(k)==Status_lift.NDF) )
		  )
		),
		Xor(
		  And(
			m2(i)==Status_lift.STATUS(Status.fr),
			ForAll(k, Implies(k!=i, m2(k)==Status_lift.NDF) )
		  ),
		  And(
		    Subscriber_lift.is_SUBSCRIBER(calls(i)),
		    m2(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.fr),
			ForAll(k, Implies(k!=i, m2(k)==Status_lift.NDF) )
		  )
		)
	  ),
	  And(
	    And( #R
	      m1(d3)!=Status_lift.NDF,
		  m2(d4)!=Status_lift.NDF
	    ),
	    And( #S
	      d3==d4,
		  m1(d3)!=m2(d4)
	    )
	  )
	)
  )
)
print simplify(Subscriber_lift.get_subscriber(Subscriber_lift.NDF))
print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 21: (With Negation)
#ClearSpeak: enumeration map injectivity obligation @ in 'EXCH' (telephone.vdmsl) at line 68:28
#((i in set (dom (status :> {<SI>}))) => (forall m1, m2 in set {{i |-> <fr>}, {calls(i) |-> <un>}} & (forall d3 in set (dom m1), d4 in set (dom m2) & ((d3 = d4) => (m1(d3) = m2(d4))))))
"""
The proof obligation is the form:
  ForAll[i,r,status,calls] (P -> ForAll[m1,m2] (Q -> ForAll[d3,d4] (R -> S) ) )
After negated, the obligation becomes the form:
  Exists[i,r,status,calls] (P and Exists[m1,m2] (Q and Exists[d3,d4] (R and Not(S)) ) )  
Where,
  P: (i in set (dom (status :> {<SI>})))
  Q: m1, m2 in set {{i |-> <fr>}, {calls(i) |-> <un>}}
  R: d3 in set (dom m1), d4 in set (dom m2)
  S: (d3 = d4) => (m1(d3) = m2(d4))
"""
print "\nTelephone: proof obligation 21"
start_time = time.clock()
s.push()
#r  = Const('r',Subscriber)
m1 = Function('m1',Subscriber,Status_lift)
m2 = Function('m2',Subscriber,Status_lift)
d3 = Const('d3',Subscriber)
d4 = Const('d4',Subscriber)

k  = Const('k',Subscriber)

s.add( # constraint of inversible map (calls) : if a subscriber is defined in domain of calls, the range cannot be itself
  ForAll(k,
    Implies(
	  calls(k)!=Subscriber_lift.NDF,
	  Subscriber_lift.get_subscriber(calls(k))!=k
	)
  )
)

s.add(
  And(
    status(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.SI)), #P
	And(
	  And( #Q
		Xor(
		  And(
		    m1(i)==Status_lift.STATUS(Status.fr),
			ForAll(k, Implies(k!=i, m1(k)==Status_lift.NDF) )
		  ),
		  And(
		    Subscriber_lift.is_SUBSCRIBER(calls(i)),
		    m1(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.un),
			ForAll(k, Implies(k!=r, m1(k)==Status_lift.NDF) )
		  )
		),
		Xor(
		  And(
			m2(i)==Status_lift.STATUS(Status.fr),
			ForAll(k, Implies(k!=i, m2(k)==Status_lift.NDF) )
		  ),
		  And(
		    Subscriber_lift.is_SUBSCRIBER(calls(i)),
		    m2(Subscriber_lift.get_subscriber(calls(i)))==Status_lift.STATUS(Status.un),
			ForAll(k, Implies(k!=i, m2(k)==Status_lift.NDF) )
		  )
		)
	  ),
	  And(
	    And( #R
	      m1(d3)!=Status_lift.NDF,
		  m2(d4)!=Status_lift.NDF
	    ),
	    And( #S
	      d3==d4,
		  m1(d3)!=m2(d4)
	    )
	  )
	)
  )
)
print simplify(Subscriber_lift.get_subscriber(Subscriber_lift.NDF))
print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 25: (With Negation)
#Suspend: enumeration map injectivity obligation @ in 'EXCH' (telephone.vdmsl) at line 75:28
#((r in set (dom (status :> {<SR>}))) => (forall m1, m2 in set {{r |-> <WR>}, {(inverse calls)(r) |-> <WI>}} & (forall d3 in set (dom m1), d4 in set (dom m2) & ((d3 = d4) => (m1(d3) = m2(d4))))))
"""
The proof obligation is the form:
  ForAll[i,r,status,calls] (P -> ForAll[m1,m2] (Q -> ForAll[d3,d4] (R -> S) ) )
After negated, the obligation becomes the form:
  Exists[i,r,status,calls] (P and Exists[m1,m2] (Q and Exists[d3,d4] (R and Not(S)) ) )  
Where,
  P: (r in set (dom (status :> {<SR>})))
  Q: m1, m2 in set {{r |-> <WR>}, {(inverse calls)(r) |-> <WI>}}
  R: d3 in set (dom m1), d4 in set (dom m2)
  S: (d3 = d4) => (m1(d3) = m2(d4))
"""
print "\nTelephone: proof obligation 25"
start_time = time.clock()
s.push()
r  = Const('r',Subscriber)
j  = Const('j',Subscriber)
m1 = Function('m1',Subscriber,Status_lift)
m2 = Function('m2',Subscriber,Status_lift)
d3 = Const('d3',Subscriber)
d4 = Const('d4',Subscriber)

k  = Const('k',Subscriber)
l  = Const('l',Subscriber)

# constraint of inversible map (calls) : s1==s2 -> calls(s1)==calls(s2), s1!=s2 -> calls(s1)!=calls(s2) or (calls(s1)==calls(s2)==NDF)
# if seems this is not sufficient, becaue Z3 give a model with a subscriber calls to itself
# this is not OK for a telephone exchange system, while is OK for a inmap
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
    status(r)==Status_lift.STATUS(Status.RECIPIENT(Recipient.SR)), # P
	And(
	  And( #Q
		Xor(
		  And(
		    m1(r)==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR)),
			ForAll(k, Implies(k!=r, m1(k)==Status_lift.NDF) )
		  ),
		  And(
		    #calls(i)!=Subscriber_lift.NDF, # inverse map is not empty
			Subscriber_lift.is_SUBSCRIBER(calls(i)),
		    Subscriber_lift.get_subscriber(calls(i)) == r, # inverse_calls(r) == i
			#i!=r,
		    m1(i)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
			ForAll(k, Implies(k!=i, m1(k)==Status_lift.NDF) )
		  )
		),
		Xor(
		  And(
		    m2(r)==Status_lift.STATUS(Status.RECIPIENT(Recipient.WR)),
			ForAll(k, Implies(k!=r, m2(k)==Status_lift.NDF) )
		  ),
		  And(
		    #calls(j)!=Subscriber_lift.NDF, # inverse map is not empty
			Subscriber_lift.is_SUBSCRIBER(calls(j)),
		    Subscriber_lift.get_subscriber(calls(j)) == r, # inverse_calls(r) == j
			#j!=r,
		    m2(j)==Status_lift.STATUS(Status.INITIATOR(Initiator.WI)),
			ForAll(k, Implies(k!=j, m2(k)==Status_lift.NDF) )
		  )
		)
	  ),
	  And(
	    And( #R
	      m1(d3)!=Status_lift.NDF,
		  m2(d4)!=Status_lift.NDF
	    ),
	    And( #S
	      d3==d4,
		  m1(d3)!=m2(d4)
	    )
	  )
	)
  )
)
#s.add(calls(Subscriber.s1)==Subscriber_lift.SUBSCRIBER(Subscriber.s2))

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))

from z3 import *
import time

s = Solver()

#types
Event_lift, (A, V, nil, NDF) = EnumSort('Event_lift', ['A', 'V', 'nil', 'NDF'])
Trace = ArraySort(IntSort(),Event_lift)

#state veriable mk_Pacemaker(aperiod,vdelay)
aperiod = Int('aperiod')
s.add(aperiod>=0) # nat
vdelay = Int('vdelay')
s.add(vdelay>=0)  # nat

#variable tr: Trace
tr = Const('tr',Trace)

#constraints of sequence
[i,j] = Ints('i j')

#Index i must from 0, trace is undefined when i below 0
s.add(
  ForAll(i, Implies( i<=0, tr[i]==NDF ) )
)

#trace should be within a index range from 0 to its length 
s.add(
  ForAll(i, #if an index is defined, all indices lower then it are defined.
    Implies(
      And(i>=1,tr[i]!=NDF),
      ForAll(j,
        Implies(And(j>=1,j<=i),tr[j]!=NDF)
      )
    )
  ),
  ForAll(i, #if an index is undefined, all indices higher then it are undefined.
    Implies(
      And(i>=1,tr[i]==NDF),
      ForAll(j,
        Implies(j>=i,tr[j]==NDF)
      )
    )
  )
)

# defined len as a function
len_tr = Function('len_tr',Trace,IntSort())
#s.add(
#  ForAll(tr, len_tr(tr)>=0)
#)
s.add(
  Or(
    And(
      len_tr(tr)==0,
      tr[1]==NDF
    ),
    And(
      len_tr(tr)>0,
      tr[len_tr(tr)]!=NDF,
      tr[len_tr(tr)+1]==NDF
    )
  )
)
#s.push()
#s.add(len_tr(tr)==1)
#s.check()
#print s.model()
#s.pop()


#Proof Obligation 1
#FaultyHeart: type compatibility obligation @ in 'DEFAULT' (AbstractPacemaker.vdmsl) at line 30:22
#(((len tr) = 100) => (aperiod > 0))
"""
The proof obligation is in the form:
  ForAll[tr,aperiod] (P -> Q)
After negated, the obligation becomes the form:
  Exists[tr,aperiod] (P and Not(Q))
Where,
  P: ((len tr) = 100)
  Q: (aperiod > 0)
"""
print "\nAbstractPacemaker: proof obligation 1"
start_time = time.clock()
s.push()
s.add(
  And(
    len_tr(tr)==100,
    Not(aperiod > 0)
  )
)

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 2
#FaultyHeart: type compatibility obligation @ in 'DEFAULT' (AbstractPacemaker.vdmsl) at line 31:26
#(((len tr) = 100) => (Periodic(tr, <A>, aperiod) => (aperiod > 0)))
"""
The proof obligation is in the form:
  ForAll[tr,aperiod] (P -> Q)
After negated, the obligation becomes the form:
  Exists[tr,aperiod] (P and Not(Q))
Where,
  P: ((len tr) = 100)
  Q: (Periodic(tr, <A>, aperiod) => (aperiod > 0))
"""
print "\nAbstractPacemaker: proof obligation 2"
start_time = time.clock()
s.push()
s.add(
  And(
    len_tr(tr)==100,
    And(
      aperiod >= 1, # Periodic: Trace * Event * nat1 -> bool
      Not(aperiod > 0)
    )
  )
)

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 3
#FaultyHeart: operation postcondition satisfiable obligation @ in 'DEFAULT' (AbstractPacemaker.vdmsl) at line 28:1
#(exists tr:Trace & post_FaultyHeart(oldstate, tr, oldstate, newstate))
"""
The proof obligation is in the form:
  ForAll[oldstate] Exists[tr,newstate] post_FaultHeart
Where,
  post_FaultyHeart:
    len tr = 100  and  Periodic(tr,<A>,aperiod)  and  (not Periodic(tr,<V>,aperiod))
Since FaultHeart does not have oldstate in its postcondition, this proof obligation is not necessary be neagted.
So we have the proof obligation:
  Exists[tr,newstate] post_FaultHeart
"""
print "\nAbstractPacemaker: proof obligation 3"
start_time = time.clock()
s.push()
# Periodic
t = Int('t')
s.add(len_tr(tr)==100)
s.add(aperiod >= 1)
s.add(
  ForAll(t,
    Implies(
      And(t>=1, t<=len_tr(tr)), # t in set inds tr
      Implies(
        tr[t] == A, # tr(t) = e
        Implies(
          t + aperiod <= len_tr(tr), # t + p <= len tr
          And(
            And(
              tr[t+aperiod] == A, # tr(t+p) = e 
              ForAll(i, # forall i in set {t+1, ..., t+p-1} & tr(i) <> e)
                Implies(
                  And(i>=t+1,i<=t+aperiod-1),
                  tr[i] != A
                )
              )
            ),
            Implies(
              t+aperiod > len_tr(tr), # t + p > len tr
              ForAll(i, # forall i in set {t+1, ..., len tr} & tr(i) <> e
                Implies(
                  And(i>=t+1,i<=len_tr(tr)),
                  tr[i] != A
                )
              )
            )
          )
        )
      )
    )
  )
)

s.add(
  Not(
    ForAll(t,
      Implies(
        And(t>=1, t<=len_tr(tr)), # t in set inds tr
        Implies(
          tr[t] == V, # tr(t) = e
          Implies(
            t + aperiod <= len_tr(tr), # t + p <= len tr
            And(
              And(
                tr[t+aperiod] == V, # tr(t+p) = e 
                ForAll(i, # forall i in set {t+1, ..., t+p-1} & tr(i) <> e)
                  Implies(
                    And(i>=t+1,i<=t+aperiod-1),
                    tr[i] != V
                  )
                )
              ),
              Implies(
                t+aperiod > len_tr(tr), # t + p > len tr
                ForAll(i, # forall i in set {t+1, ..., len tr} & tr(i) <> e
                  Implies(
                    And(i>=t+1,i<=len_tr(tr)),
                    tr[i] != V
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)


"""
Periodic: Trace * Event * nat1 -> bool

  forall t in set inds tr &
     (tr(t) = e) =>
       (t + p <= len tr =>
       ((tr(t+p) = e and forall i in set {t+1, ..., t+p-1} & tr(i) <> e))
       and
       (t + p > len tr =>
         forall i in set {t+1, ..., len tr} & tr(i) <> e));

ForAll[t] P -> ( Q -> (R -> ( S and (T -> U) ) ) )
P: t in set inds tr
Q: tr(t) = e
R: t + p <= len tr
S: ((tr(t+p) = e and forall i in set {t+1, ..., t+p-1} & tr(i) <> e))
T: t + p > len tr
U: forall i in set {t+1, ..., len tr} & tr(i) <> e)
"""

print s
#print "skip check....."
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 4
#Periodic: legal sequence application obligation @ in 'DEFAULT' (AbstractPacemaker.vdmsl) at line 38:7
#(forall tr:Trace, e:Event, p:nat1 & (forall t in set (inds tr) & (t in set (inds tr))))
"""
The proof obligation is in the form:
  ForAll[tr,e,p] ForAll[t] (P -> Q)
Where e:Event, p:nat1, t:nat
After negated, the obligation becomes the form:
  Exists[tr,e,p,t] (P and Not(Q))
Where,
  P: t in set (inds tr)
  Q: t in set (inds tr) # ???
"""
print "\nAbstractPacemaker: proof obligation 4"
start_time = time.clock()
s.push()
e = Const('e',Event_lift)
s.add(e!=NDF)
p = Int('p')
s.add(p>=1)
t = Int('t')
s.add(t>=0)
s.add(
  And(
    And(t>=1, t<=len_tr(tr)),
    Not(And(t>=1, t<=len_tr(tr)))
  )
)

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 5
#Periodic: legal sequence application obligation @ in 'DEFAULT' (AbstractPacemaker.vdmsl) at line 40:8
#(forall tr:Trace, e:Event, p:nat1 & (forall t in set (inds tr) & ((tr(t) = e) => (((t + p) <= (len tr)) => ((t + p) in set (inds tr))))))
"""
The proof obligation is in the form:
  ForAll[tr,e,p] ForAll[t] (P -> (Q -> (R -> S) ) )
Where e:Event, p:nat1, t:nat
After negated, the obligation becomes the form:
  Exists[tr,e,p,t] (P and Q and R and Not(S))
Where,
  P: t in set (inds tr)
  Q: (tr(t) = e)
  R: ((t + p) <= (len tr))
  S: ((t + p) in set (inds tr))
"""
print "\nAbstractPacemaker: proof obligation 5"
start_time = time.clock()
s.push()
e = Const('e',Event_lift)
s.add(e!=NDF)
p = Int('p')
s.add(p>=1)
t = Int('t')

s.add(And(t>=1, t<=len_tr(tr))) #P
s.add(tr[t]==e) #Q
s.add((t+p)<=len_tr(tr)) #R
s.add(Not(And(t+p>=1,t+p<=len_tr(tr)))) #not S

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 6
#Periodic: legal sequence application obligation @ in 'DEFAULT' (AbstractPacemaker.vdmsl) at line 41:44
#(forall tr:Trace, e:Event, p:nat1 & (forall t in set (inds tr) & ((tr(t) = e) => (((t + p) <= (len tr)) => ((tr((t + p)) = e) => (forall i in set {(t + 1), ... ,((t + p) - 1)} & (i in set (inds tr))))))))
"""
The proof obligation is in the form:
  ForAll[tr,e,p] ForAll[t] (P -> (Q -> (R -> S -> (ForAll[i] T -> U) ) ) )
Where e:Event, p:nat1, t:nat
After negated, the obligation becomes the form:
  Exists[tr,e,p,t,i] (P and Q and R and S and T and Not(U))
Where,
  P: t in set (inds tr)
  Q: (tr(t) = e)
  R: ((t + p) <= (len tr))
  S: (tr((t + p)) = e)
  T: i in set {(t + 1), ... ,((t + p) - 1)}
  U: (i in set (inds tr))
"""
print "\nAbstractPacemaker: proof obligation 6"
start_time = time.clock()
s.push()
e = Const('e',Event_lift)
s.add(e!=NDF)
p = Int('p')
s.add(p>=1)
t = Int('t')

s.add(And(t>=1, t<=len_tr(tr))) #P
s.add(tr[t]==e) #Q
s.add((t+p)<=len_tr(tr)) #R
s.add(And(t+p>=1,tr[t+p]==e)) #not S
s.add(And(i>=t+1,i<=(t+p)-1)) #not T
s.add(Not(And(t+p>=1,t+p<=len_tr(tr)))) #not U

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 7
#Periodic: legal sequence application obligation @ in 'DEFAULT' (AbstractPacemaker.vdmsl) at line 44:45
#(forall tr:Trace, e:Event, p:nat1 & (forall t in set (inds tr) & ((tr(t) = e) => (((t + p) <= (len tr)) => (((tr((t + p)) = e) and (forall i in set {(t + 1), ... ,((t + p) - 1)} & (tr(i) <> e))) => (((t + p) > (len tr)) => (forall i in set {(t + 1), ... ,(len tr)} & (i in set (inds tr)))))))))
"""
The proof obligation is in the form:
  ForAll[tr,e,p] ForAll[t] (P -> (Q -> (R -> S -> (ForAll[i] T -> U) ) ) )
Where e:Event, p:nat1, t:nat
After negated, the obligation becomes the form:
  Exists[tr,e,p,t,i] (P and Q and R and S and T and Not(U))
Where,
  P: t in set (inds tr)
  Q: (tr(t) = e)
  R: ((t + p) <= (len tr))
  S: ((tr((t + p)) = e) and (forall i in set {(t + 1), ... ,((t + p) - 1)} & (tr(i) <> e)))
  T: ((t + p) > (len tr))
  U: (forall i in set {(t + 1), ... ,(len tr)} & (i in set (inds tr)))  # use j for ForAll[i]
"""
print "\nAbstractPacemaker: proof obligation 7"
start_time = time.clock()
s.push()
e = Const('e',Event_lift)
s.add(e!=NDF)
p = Int('p')
s.add(p>=1)
t = Int('t')
j = Int('j')

s.add(And(t>=1, t<=len_tr(tr))) #P
s.add(tr[t]==e) #Q
s.add((t+p)<=len_tr(tr)) #R
s.add(And(t+p>=1,tr[t+p]==e)) #S1
s.add( #S2
  ForAll(i,
    Implies(
      And(i>=t+1,i<=(t+p)+1),
      tr[i] != e
    )
  )
)
s.add(And(t+p>=1,t+p>len_tr(tr))) #T
s.add( #not U (use j instead of i)
  And(j>=t+1,j<=len_tr(tr)),
  Not(And(j>=1,j<=len_tr(tr)))
)

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 8
#Pace: legal sequence application obligation @ in 'DEFAULT' (AbstractPacemaker.vdmsl) at line 55:44
#(forall tr:Trace, aperi:nat1, vdel:nat1, oldstate:DEFAULT`Pacemaker & (forall i in set (inds (tl tr)) & (((i mod aperi) = (vdel + 1)) => (i in set (inds tr)))))
"""
The proof obligation is in the form:
  ForAll[tr,aperi,vdel,oldstate] ForAll[i] (P -> (Q -> R) )
Where aperi:nat1, vdel:nat1
After negated, the obligation becomes the form:
  Exists[tr,aperi,vdel,i] (P and Q and Not(R) )
Where,
  P: i in set (inds (tl tr))
  Q: ((i mod aperi) = (vdel + 1))
  R: (i in set (inds tr))
"""
print "\nAbstractPacemaker: proof obligation 8"
start_time = time.clock()
s.push()
aperi = Int('aperi')
s.add(aperi>=1)
vdel = Int('vdel')
s.add(vdel>=1)

s.add(And(i>=1, i<=len_tr(tr)-1)) #P
s.add(i%aperi==vdel+1) #Q
s.add(Not(And(i>=1,i<=len_tr(tr)))) #not R

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))


#Proof Obligation 9
#Pace: non-empty sequence obligation @ in 'DEFAULT' (AbstractPacemaker.vdmsl) at line 58:29
#(forall tr:Trace, aperi:nat1, vdel:nat1, oldstate:DEFAULT`Pacemaker & (tr <> []))
"""
The proof obligation is in the form:
  ForAll[tr,aperi,vdel,oldstate] P
Where aperi:nat1, vdel:nat1
After negated, the obligation becomes the form:
  Exists[tr,aperi,vdel] Not(P)
Where,
  P: (tr <> [])
"""
print "\nAbstractPacemaker: proof obligation 9"
s.push()
aperi = Int('aperi')
s.add(aperi>=1)
vdel = Int('vdel')
s.add(vdel>=1)

s.add(Not(len_tr(tr)>0)) #not P

print s
res = s.check()
print res
if res == sat: print 'model:', s.model()
s.pop()
print("--- %s seconds ---\n" % (time.clock() - start_time))

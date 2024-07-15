To fix the relational symbolic execution we need to do the following:
1. Make sure the product domain has the same type as the normal symbolic domain.
  - I think technically we want the product symbolic execution to have the same signature as the sound symbolic execution.
2. Once these have the same signature, we make sure that the relational execution is parametric.
3. Finally, we have to somehow define relational states that depend on the non-relational states.

1 and 2 are easy. The problem is doing 3.
For 3 the thing is that we have many choices, where the most obvious one is to
define relational states as pairs of non-relational states.
Options:
- Obvious: RelState = State * State
- What if we define types of states? For example, we have "symbolic states"
which we know how to handle. Then we have, numerical states such as intervals.
Then product states are: symbolic state * numerical state
Finally, relational states can be somewhat as I wanted.

I like the second idea. It is basically implemented at this point by the things
done.

So plan for today: I will rework the definition of state in its own interface.
Then apply it everywhere.
BUT FIRST: check this idea for numerical. Is it doable?
Numerical states are not the problem since they are always the same.

Options states are:
- symbolic state = svm * sp (symst)
- numerical state = constrs
- product state = symst * constrs
- relational state = svm^2 * sp
<!-- - relational product state = (svm^2 * sp ) * numstate * numstate -->
<!-- - relational product state = ((svm * sp ) * numstate) * ((svm * sp ) * numstate) -->
- relational product state = ((svm^2 * sp ) * (numstate * numstate)
I think this is the logical way.
So the thing is that the relational domain needs to really understand the structure of the SE state.
Options are:
SE state is svm * sp or
SE state is (svm * sp) * numstate
The other thing to keep in mind is that P is in SP, so we cannot define SVM taking that P and the relating to SP, but rather SVM needs to defined from SP.

The problem is that if we define SVM module, it takes the SP, and then we have a problem if we define an SVM for relational states.

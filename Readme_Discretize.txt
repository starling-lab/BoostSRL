As RDN Boost model accepts discrete values in its input predicate logic form, a new discretization functionality has been added as follows;

1. In the mode file, user has to specify the predicate and its arguments to discretize along with the number of bins desired. The discretization uses equal frequency distribution. An example from background file is mentioned below:

For the following predicate
hdl(+Patient,#Time, #hdlValue).
 
We want to discretize the 2nd and 3rd argument and into 2 and 3 bins respectively.
disc: hdl([2,3],[2,3]).

Another example 
For a predicate 
a1c(+Patient,+a1cValue).

We want to discretize the 1rst argument and into 4 bins.
disc: a1c([2],[4]).

Another example is when user doesn't want to specify the number of bins. 
Here, we use Sturge's formula which assumes an approximate normal distribution over the continuous values to be discretized, to pick the optimal number of bins.
User should give "d" against the argument She/he wants to discretize using default parameter.

Ex. disc: hdl([2,3],[d,3]).

This means the argument 2 has to be discretized with default number of bins and argument 3 has to be discretized into 3 bins.

In case, User wants to discretize less than 8 values, we default the number of bins to 2.

  



 
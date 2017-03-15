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



 
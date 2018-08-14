include "globals.mzn";

% Model Input
int: n;
array[1..n, 1..2] of 0..1000: coords;

% Internal data
int: distvector = (n * (n-1)) div 2;
array[1..distvector] of int: dist = [calc_distance(i,j) | i in 1..n, j in (i+1)..n];

array[1..n] of var 1..n: succ;
array[1..n] of var int: trip_length;
array[1..n] of var 1..n: trip;

function int: calc_distance(1..n: i, 1..n: j) =
  let {
    int: xdiff = coords[i,1] - coords[j,1],
    int: ydiff = coords[i,2] - coords[j,2]
  } in
  round(sqrt(xdiff*xdiff + ydiff*ydiff));

predicate set_trip_length(var int: i, var int: j) = 
  let {
    var int: a = max(i, j)-1,
    var int: b = min(i, j)-1,
    var int: idx = n * b - b * (b + 1) div 2 + a - b
  } in
  trip_length[i] = dist[idx];

constraint forall(i in 1..n) (set_trip_length(i, succ[i]));

% Main constraints to enforce tsp trip
% This is just the MiniZinc decomposition of circuit/1, but we are interested in the trip
constraint alldifferent(succ);	
constraint alldifferent(trip);
constraint forall(i in 1..n)(succ[i] != i);
constraint trip[1] = 1;
constraint forall(i in 1..n)(trip[i] != n -> trip[succ[i]] = trip[i] + 1);
constraint forall(i in 1..n)(trip[i] == n -> succ[i] = 1 );

% Redundant, but allows each solver to use their own decomposition for circuit/1
constraint redundant_constraint(circuit(succ));

% Naive upper bound to reduce objective domain size
int: ub = sum([calc_distance(i,i+1) | i in 1..n-1]) + calc_distance(n,1);
var 0..ub: objective = sum(trip_length);

ann: boundestann;

solve 
  :: seq_search([
    boundestann, 
    int_search(trip, input_order, indomain_min, complete)
  ])
  minimize objective;

output [
"trip = " ++ show(trip) ++ ";\n" ++
"objective = " ++ show(objective) ++ ";"];
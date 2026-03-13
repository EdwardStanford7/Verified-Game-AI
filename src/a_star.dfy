include "utils.dfy"

module AStar {
  import opened Utils

  // Given an agent's position, a list of goal positions, and a grid representing
  // the environment, determine the optimal path to the closest goal using A*.
  method A_Star(grid: Grid, agent_position: Point, goals: seq<Point>) returns (path: seq<Point>)
  {
    path := [];
    // UNIMPLEMENTED NOT DEALING WTH THIS YET UNTIL VISIBILITY IS WORKING
  }
}
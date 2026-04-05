include "utils.dfy"
include "visibility.dfy"
include "a_star.dfy"

module Pathfind {
  import Utils = Utils`Public
  import UtilsPrivate = Utils`Internal
  import opened Visibility
  import opened AStar

  export
    provides Utils
    reveals Pathfinder
    provides Pathfinder.grid, Pathfinder.Valid, Pathfinder.Pathfind

  class Pathfinder<T> {
    const grid: array2<T>
    const rectangles: seq<UtilsPrivate.Rectangle>
    const visibility_blocking: T -> bool
    const traversable: T -> bool

    ghost predicate Valid()
      reads this, grid
    {
      forall j :: 0 <= j < |rectangles| ==>
                    UtilsPrivate.RectangleInRange(rectangles[j], grid)
    }

    constructor(grid: array2<T>, visibility_blocking: T -> bool, traversable: T -> bool)
      ensures this.grid == grid
      ensures Valid()
    {
      var rectangles0 := ExtractBlockingRectangles(grid, visibility_blocking);
      this.grid := grid;
      this.rectangles := rectangles0;
      this.visibility_blocking := visibility_blocking;
      this.traversable := traversable;
    }

    method Pathfind(
      agent_position: Utils.Point,
      value: (Utils.Point, Utils.Point, T) -> real)
      returns (path: seq<Utils.Point>, visible: array2<bool>)
      requires Valid()
      requires Utils.ValidPoint(agent_position, grid)
      ensures Valid()
      ensures grid.Length0 == visible.Length0 && grid.Length1 == visible.Length1
      ensures forall p :: p in path ==> Utils.ValidPoint(p, grid)
    {
      var rectangles_array := new UtilsPrivate.Rectangle[|rectangles|](
                                                         i requires 0 <= i < |rectangles| => rectangles[i]);
      assert forall j :: 0 <= j < rectangles_array.Length ==> UtilsPrivate.RectangleInRange(rectangles_array[j], grid) by {
        forall j | 0 <= j < rectangles_array.Length
          ensures UtilsPrivate.RectangleInRange(rectangles_array[j], grid)
        {
          assert rectangles_array[j] == rectangles[j];
        }
      }
      var extended_rectangles := [];
      visible, extended_rectangles := CalculateFOV(grid, rectangles_array, agent_position);
      var goal := GetGoal(visible, value, agent_position);
      path := A_Star(grid, agent_position, goal, traversable);
    }

    // Call once during initialization to extract rectangles from the grid,
    // then reuse that cached sequence for future FOV calls.
    static method ExtractBlockingRectangles(grid: array2<T>, visibility_blocking: T -> bool)
      returns (rectangles: seq<UtilsPrivate.Rectangle>)
      ensures forall i :: 0 <= i < |rectangles| ==> UtilsPrivate.RectangleInRange(rectangles[i], grid)
      ensures forall i :: 0 <= i < |rectangles| ==> UtilsPrivate.RectangleMatchesGrid(rectangles[i], grid, visibility_blocking)
    {
      rectangles := [];
      var visited := new bool[grid.Length0, grid.Length1]((i, j) => false);

      for x := 0 to grid.Length0
        invariant forall r :: r in rectangles ==> UtilsPrivate.RectangleInRange(r, grid)
        invariant forall r :: r in rectangles ==> UtilsPrivate.RectangleMatchesGrid(r, grid, visibility_blocking)
      {
        for y := 0 to grid.Length1
          invariant forall r :: r in rectangles ==> UtilsPrivate.RectangleInRange(r, grid)
          invariant forall r :: r in rectangles ==> UtilsPrivate.RectangleMatchesGrid(r, grid, visibility_blocking)
        {
          if visibility_blocking(grid[x, y]) && !visited[x, y] {

            var x_size := 0;
            while x + x_size < grid.Length0 && visibility_blocking(grid[x + x_size, y]) && !visited[x + x_size, y]
              invariant x + x_size <= grid.Length0
              invariant forall xx :: x <= xx < x + x_size ==> visibility_blocking(grid[xx, y])
            {
              x_size := x_size + 1;
            }

            var y_size := 1;
            while y + y_size < grid.Length1 &&
              (forall xx {:trigger grid[xx, y + y_size]} :: x <= xx < x + x_size ==>
              visibility_blocking(grid[xx, y + y_size]) && !visited[xx, y + y_size])
              invariant 1 <= y_size <= grid.Length1 - y
              invariant y + y_size <= grid.Length1
              invariant forall xx, yy :: x <= xx < x + x_size && y <= yy < y + y_size ==>
                                           visibility_blocking(grid[xx, yy])
            {
              y_size := y_size + 1;
            }

            // Mark visited.
            for xx := x to x + x_size {
              for yy := y to y + y_size {
                visited[xx, yy] := true;
              }
            }

            rectangles := rectangles + [UtilsPrivate.Rectangle(x, y, x + x_size, y + y_size)];
          }
        }
      }
    }

    method GetGoal(
      visible: array2<bool>,
      value_function: (Utils.Point, Utils.Point, T) -> real,
      agent_position: Utils.Point)
      returns (goal: Utils.Point)
      requires grid.Length0 == visible.Length0 && grid.Length1 == visible.Length1
    {
      goal := agent_position; // Default to current position if no visible cell has value > 0.

      var best_value := 0.0;

      for x := 0 to grid.Length0 {
        for y := 0 to grid.Length1 {
          if visible[x, y] {
            var value := value_function(agent_position, Utils.Point(x, y), grid[x, y]);
            if value > best_value {
              best_value := value;
              goal := Utils.Point(x, y);
            }
          }
        }
      }
    }
  }
}

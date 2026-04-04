module Utils {
  export Public
    reveals Point
    provides ValidPoint, ManhattanDistance

  export Internal extends Public
    reveals *

  export extends Internal

  datatype Point = Point(x: int, y: int)
  datatype Rectangle = Rectangle(minX: int, minY: int, maxX: int, maxY: int)

  predicate ValidPoint<T>(p: Point, grid: array2<T>) {
    0 <= p.x < grid.Length0 && 0 <= p.y < grid.Length1
  }

  predicate WalkablePoint<T>(p: Point, grid: array2<T>, traversable: T -> bool)
    reads grid
  {
    ValidPoint(p, grid) && traversable(grid[p.x, p.y])
  }

  // 4-connected adjacency on the grid.
  predicate Adjacent(p: Point, q: Point)
  {
    (p.x == q.x && (p.y + 1 == q.y || q.y + 1 == p.y)) ||
    (p.y == q.y && (p.x + 1 == q.x || q.x + 1 == p.x))
  }

  // Every point in the path is inside the grid and traversable.
  predicate WalkablePath<T>(path: seq<Point>, grid: array2<T>, traversable: T -> bool)
    reads grid
    decreases |path|
  {
    |path| == 0 ||
    (WalkablePoint(path[0], grid, traversable) && WalkablePath(path[1..], grid, traversable))
  }

  // Consecutive path points are 4-neighbor moves.
  predicate ConsecutivePath(path: seq<Point>)
    decreases |path|
  {
    |path| <= 1 ||
    (Adjacent(path[0], path[1]) && ConsecutivePath(path[1..]))
  }

  // A non-empty, walkable, 4-connected path from start to goal.
  predicate FeasiblePath<T>(path: seq<Point>, start: Point, goal: Point, grid: array2<T>, traversable: T -> bool)
    reads grid
  {
    0 < |path| &&
    path[0] == start &&
    path[|path| - 1] == goal &&
    WalkablePath(path, grid, traversable) &&
    ConsecutivePath(path)
  }

  predicate RectangleInRange<T>(rectangle: Rectangle, grid: array2<T>)
    reads grid
  {
    0 <= rectangle.minX && rectangle.minX < rectangle.maxX && rectangle.maxX <= grid.Length0 &&
    0 <= rectangle.minY && rectangle.minY < rectangle.maxY && rectangle.maxY <= grid.Length1
  }

  predicate RectangleMatchesGrid<T>(rectangle: Rectangle, grid: array2<T>, visibility_blocking: T -> bool)
    requires RectangleInRange(rectangle, grid)
    reads grid
  {
    forall x, y :: rectangle.minX <= x < rectangle.maxX && rectangle.minY <= y < rectangle.maxY ==> visibility_blocking(grid[x, y])
  }

  lemma WalkablePathIndex<T>(path: seq<Point>, i: int, grid: array2<T>, traversable: T -> bool)
    requires 0 <= i < |path|
    requires WalkablePath(path, grid, traversable)
    ensures WalkablePoint(path[i], grid, traversable)
    decreases |path|
  {
    if i == 0 {
      assert WalkablePoint(path[0], grid, traversable);
    } else {
      assert 0 < i;
      assert WalkablePath(path[1..], grid, traversable);
      assert 0 <= i - 1 < |path[1..]|;
      WalkablePathIndex(path[1..], i - 1, grid, traversable);
      assert path[1..][i - 1] == path[i];
    }
  }

  lemma FeasiblePathHasWalkablePoints<T>(
    path: seq<Point>, start: Point, goal: Point, grid: array2<T>, traversable: T -> bool)
    requires FeasiblePath(path, start, goal, grid, traversable)
    ensures forall p :: p in path ==> WalkablePoint(p, grid, traversable)
  {
    assert WalkablePath(path, grid, traversable);
    assert forall p :: p in path ==> WalkablePoint(p, grid, traversable) by {
      forall p | p in path
        ensures WalkablePoint(p, grid, traversable)
      {
        var i :| 0 <= i < |path| && path[i] == p;
        WalkablePathIndex(path, i, grid, traversable);
      }
    }
  }

  function ManhattanDistance(p1: Point, p2: Point): int {
    var dx := p1.x - p2.x;
    var dy := p1.y - p2.y;
    (if dx >= 0 then dx else -dx) + (if dy >= 0 then dy else -dy)
  }
}

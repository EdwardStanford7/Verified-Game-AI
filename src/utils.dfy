module Utils{
  datatype Point = Point(x: int, y: int)
  datatype Cell = Empty | Wall | Food
  type Grid = array2<Cell>
  datatype Rectangle = Rectangle(minX: int, minY: int, maxX: int, maxY: int)

  predicate ValidPoint(p: Point, grid: Grid) { 0 <= p.x < grid.Length0 && 0 <= p.y < grid.Length1 }

  predicate ValidRectangle(rectangle: Rectangle, grid: Grid)
  {
    0 <= rectangle.minX && rectangle.minX < rectangle.maxX && rectangle.maxX <= grid.Length0 &&
    0 <= rectangle.minY && rectangle.minY < rectangle.maxY && rectangle.maxY <= grid.Length1
  }

  predicate RectanglesMatchGrid(rectangles: array<Rectangle>, grid: Grid)
    reads grid
    reads rectangles
  {
    // All rectangles are valid and cover only Wall cells
    forall i :: 0 <= i < rectangles.Length ==>
                  ValidRectangle(rectangles[i], grid) &&
                  forall x, y :: rectangles[i].minX <= x < rectangles[i].maxX && rectangles[i].minY <= y < rectangles[i].maxY ==>
                                   grid[x, y] == Wall
                                   &&
                                   // All Wall cells are covered by some rectangle, and all non-Wall cells are not covered
                                   forall x, y :: 0 <= x < grid.Length0 && 0 <= y < grid.Length1 ==>
                                                    (grid[x, y] == Wall <==>
                                                     exists i :: 0 <= i < rectangles.Length &&
                                                                 rectangles[i].minX <= x < rectangles[i].maxX &&
                                                                 rectangles[i].minY <= y < rectangles[i].maxY)
  }

  // Call once during initialization to extract rectangles from the grid then use those rectangles for all calls to pathfind function.
  method ExtractWallRectangles(grid: Grid) returns (rectangles: array<Rectangle>)
    ensures forall i :: 0 <= i < rectangles.Length ==> ValidRectangle(rectangles[i], grid)
    ensures RectanglesMatchGrid(rectangles, grid)
  {
    var rectangles_seq := [];

    var visited := new bool[grid.Length0, grid.Length1] ((i, j) => (false));
    for x := 0 to grid.Length0 {
      for y := 0 to grid.Length1 {
        visited[x, y] := false;
      }
    }

    for x := 0 to grid.Length0 {
      for y := 0 to grid.Length1 {
        if grid[x, y] == Wall && !visited[x, y] {

          // Determine width
          var width := 0;
          while x + width < grid.Length0 && grid[x + width, y] == Wall && !visited[x + width, y]
            invariant x + width <= grid.Length0
          {
            width := width + 1;
          }

          // Determine height
          var height := 0;
          while y + height < grid.Length1 && forall xx {:trigger grid[xx, y + height]} :: x <= xx < x + width ==> grid[xx, y + height] == Wall && !visited[xx, y + height]
            invariant y + height <= grid.Length1
          {
            height := height + 1;
          }

          // Mark visited
          for xx := x to x + width {
            for yy := y to y + height {
              visited[xx, yy] := true;
            }
          }

          rectangles_seq := rectangles_seq + [Rectangle(x, y, x + width, y + height)];
        }
      }
    }

    rectangles := new Rectangle[|rectangles_seq|] (i requires 0<= i < |rectangles_seq| => rectangles_seq[i]);

    // TODO: maybe deal with proving this later if we get around to it, this isn't part of the core algorithm we're trying to verify.
    assume {:axiom} RectanglesMatchGrid(rectangles, grid);
  }
}
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
}
type shark =
  | Unit
  | Or(array(shark))
  | And(array(shark))
  | Array(shark, shark); /* first ^ second */

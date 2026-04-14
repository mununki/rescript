[@@@warning "-45"]

let rewrite ~(typedtree : Typedtree.structure) (ast : Parsetree.structure) :
    Parsetree.structure option =
  Comptime_eval.rewrite ~typedtree ast

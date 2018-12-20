type shark =
  | Unit
  /* | Or(array(shark))
  | And(array(shark)) */
  | Array(shark, shark); /* first ^ second */

Utils.requireCSS("src/Type.css");

let unitRef = ref(() => ReasonReact.null);
let arrayRef = ref((_base, _exp) => ReasonReact.null);

module rec Tree: {
  let component: ReasonReact.componentSpec(
    ReasonReact.stateless,
    ReasonReact.stateless,
    ReasonReact.noRetainedProps,
    ReasonReact.noRetainedProps,
    ReasonReact.actionless,
  );
  let make: (array(ReasonReact.reactElement), ~tree: shark) => ReasonReact.componentSpec(
    ReasonReact.stateless,
    ReasonReact.stateless,
    ReasonReact.noRetainedProps,
    ReasonReact.noRetainedProps,
    ReasonReact.actionless,
  );
} = {
  let component = ReasonReact.statelessComponent("Tree");
  let make = (_children, ~tree) => {
    ...component,
    render: _self =>
      <div className="Type_tree">
        (switch (tree) {
        | Unit => unitRef^();
        /* | Type.Or(orChildren) => <TypeOr orChildren />
        | Type.And(_) => <div>(ReasonReact.string("And!"))</div> */
        | Array(base, exp) => arrayRef^(base, exp);
        })
      </div>,
  };
}
and UnitView: {
  let component: ReasonReact.componentSpec(
    ReasonReact.stateless,
    ReasonReact.stateless,
    ReasonReact.noRetainedProps,
    ReasonReact.noRetainedProps,
    ReasonReact.actionless,
  );
  let make: (array(ReasonReact.reactElement)) => ReasonReact.componentSpec(
    ReasonReact.stateless,
    ReasonReact.stateless,
    ReasonReact.noRetainedProps,
    ReasonReact.noRetainedProps,
    ReasonReact.actionless,
  );
} = {
  let component = ReasonReact.statelessComponent("UnitView");
  let make = (_children) => {
    ...component,
    render: _self =>
      <div className="Type_unit">
        (ReasonReact.string("Unit!"))
      </div>,
  };
}
and ArrayView: {
  let component: ReasonReact.componentSpec(
    ReasonReact.stateless,
    ReasonReact.stateless,
    ReasonReact.noRetainedProps,
    ReasonReact.noRetainedProps,
    ReasonReact.actionless,
  );
  let make: (array(ReasonReact.reactElement), ~base: shark, ~exp: shark) => ReasonReact.componentSpec(
    ReasonReact.stateless,
    ReasonReact.stateless,
    ReasonReact.noRetainedProps,
    ReasonReact.noRetainedProps,
    ReasonReact.actionless,
  );
} = {
  let component = ReasonReact.statelessComponent("ArrayView");
  let make = (_children, ~base, ~exp) => {
    ...component,
    render: _self =>
      <div className="Type_array">
        <Tree tree=base />
        <Tree tree=exp />
      </div>,
  };
};

unitRef := (() => ReasonReact.element(UnitView.make([||])));
arrayRef := ((base, exp) => ReasonReact.element(ArrayView.make([||], ~base, ~exp)));

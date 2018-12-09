let component = ReasonReact.statelessComponent("TypeRoot");

let make = (~root, _children) => {
  ...component,
  render: _self =>
    switch (root) {
    | Type.Unit => <TypeUnit />
    | Type.Or(orChildren) => <TypeOr orChildren />
    | Type.And(_) => <div>(ReasonReact.string("And!"))</div>
    | Type.Array(_) => <div>(ReasonReact.string("Array!"))</div>
    },
};

let component = ReasonReact.statelessComponent("TypeUnit");

let make = (~orChildren, _children) => {
  ...component,
  render: _self =>
    <div>
      (ReasonReact.array(
        Array.map(_orChild => <div>(ReasonReact.string("child"))</div>, orChildren)))
    </div>
};

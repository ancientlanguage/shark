let component = ReasonReact.statelessComponent("ValuesPage");

let make = _children => {
  ...component,
  render: _self =>
    <div>
      (ReasonReact.string("Values!"))
    </div>
};

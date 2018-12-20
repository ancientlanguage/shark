type state = Type.shark;

type action =
  | ChangeType;

let reducer = (action, _state) =>
  switch (action) {
  | ChangeType => ReasonReact.Update(Type.Unit)
  };

let component = ReasonReact.reducerComponent("HomePage");

let make = _children => {
  ...component,
  reducer,
  initialState: () => Type.Array(Type.Unit, Type.Array(Type.Unit, Type.Unit)),
  render: self => <Type.Tree tree=self.state />
};

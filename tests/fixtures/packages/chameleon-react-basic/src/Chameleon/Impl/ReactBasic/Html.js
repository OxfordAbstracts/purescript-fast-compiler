import * as React from "react";

export const createElement = (name) => (props) => (kids) =>
  React.createElement(name, props, ...kids);

export const createVoidElement = (name) => (props) =>
  React.createElement(name, props);

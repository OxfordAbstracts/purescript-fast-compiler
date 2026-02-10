import Enzyme from 'enzyme';

export function configure_(adapter) {
  Enzyme.configure({ adapter: adapter() })
}

export var mount_ = Enzyme.mount;

export function at_(index, wrapper) {
  return wrapper.at(index);
}

export function debug_(wrapper) {
  return wrapper.debug();
}

export function exists_(selector, wrapper) {
  return wrapper.exists(selector);
}

export function find_(selector, wrapper) {
  return wrapper.find(selector);
}

export function parent_(wrapper) {
  return wrapper.parent();
}

export function children_(wrapper) {
  return wrapper.children();
}

export function childAt_(idx, wrapper) {
  return wrapper.childAt(idx);
}

export function is_(selector, wrapper) {
  return wrapper.is(selector);
}

export function length(wrapper) {
  return wrapper.length;
}

export function prop_(key, wrapper) {
  return wrapper.prop(key);
}

export function unsafeSetState_(newState, wrapper) {
  return (_onError, onSuccess) => {
    wrapper.setState(newState, onSuccess)

    return (_cancelError, _onCancelerError, onCancelerSuccess) => {
      onCancelerSuccess()
    }
  }
}

export function simulate_(eventType, event, wrapper) {
  return wrapper.simulate(eventType, event);
}

export function simulateCustom_(eventType, event, wrapper) {
  return wrapper.getElement().props[eventType](event);
}

export function state_(wrapper) {
  return wrapper.state();
}

export function text_(wrapper) {
  return wrapper.text();
}

export function name_(wrapper) {
  return wrapper.name();
}

export function unmount_(wrapper) {
  return wrapper.unmount();
}

export function update_(wrapper) {
  return wrapper.update();
}

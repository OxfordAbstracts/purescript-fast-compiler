export const formatPrim_ = JSON.stringify

export const fromJsValue_ = value =>
  ["number", "string", "boolean", "undefined"].includes(typeof value)
  ? { tag: "VPrim", value }
  : value === null
  ? { tag: "VPrim", value }
  : value.constructor.name === "Array"
  ? { tag: "VArray", value: value.map(fromJsValue_) }
  : value.constructor.name === "Object"
  ? {
    tag: "VObject",
    value: sortedKeys(value).map(key => ({ key: fromJsValue_(key), value: fromJsValue_(value[key]) }))
  }
  : {
    tag: value.constructor.name,
    value: sortedKeys(value).map(key => fromJsValue_(value[key]))
  }

const sortedKeys = obj =>
  Object
  .keys(obj)
  .sort((a, b) =>
    a.localeCompare(
      b,
      undefined,
      { numeric: true }
    )
  )

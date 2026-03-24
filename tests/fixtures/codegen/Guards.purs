module Guards where

classify :: Boolean -> String
classify b
  | b = "true"
  | true = "false"

test = classify true

-- TEST: "true"

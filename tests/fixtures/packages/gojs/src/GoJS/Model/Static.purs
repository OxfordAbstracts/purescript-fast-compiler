module GoJS.Model.Static where


import Effect (Effect)
import GoJS.Model (class IsModel)
import GoJS.Unsafe (callStatic1)

-- Optional parameters excluded: model: Model
fromJson_ :: forall m. IsModel m => String -> Effect m
fromJson_ = callStatic1 "Model" "fromJson"
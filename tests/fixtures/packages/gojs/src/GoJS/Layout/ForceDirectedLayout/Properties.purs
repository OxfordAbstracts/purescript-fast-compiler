module GoJS.Layout.ForceDirectedLayout.Properties where


import GoJS.Geometry.Types (Size_)
import GoJS.Layout.Types (ForceDirectedLayout_)
import GoJS.Unsafe (getUnsafe)

_arrangementSpacing :: ForceDirectedLayout_ -> Size_
_arrangementSpacing = getUnsafe [ "arrangementSpacing" ]

_arrangesToOrigin :: ForceDirectedLayout_ -> Boolean
_arrangesToOrigin = getUnsafe [ "arrangesToOrigin" ]

_comments :: ForceDirectedLayout_ -> Boolean
_comments = getUnsafe [ "comments" ]

-- Read-only
_currentIteration :: ForceDirectedLayout_ -> Number
_currentIteration = getUnsafe [ "currentIteration" ]

_defaultCommentElectricalCharge :: ForceDirectedLayout_ -> Number
_defaultCommentElectricalCharge = getUnsafe [ "defaultCommentElectricalCharge" ]

_defaultCommentSpringLength :: ForceDirectedLayout_ -> Number
_defaultCommentSpringLength = getUnsafe [ "defaultCommentSpringLength" ]

_defaultElectricalCharge :: ForceDirectedLayout_ -> Number
_defaultElectricalCharge = getUnsafe [ "defaultElectricalCharge" ]

_defaultGravitationalMass :: ForceDirectedLayout_ -> Number
_defaultGravitationalMass = getUnsafe [ "defaultGravitationalMass" ]

_defaultSpringLength :: ForceDirectedLayout_ -> Number
_defaultSpringLength = getUnsafe [ "defaultSpringLength" ]

_defaultSpringStiffness :: ForceDirectedLayout_ -> Number
_defaultSpringStiffness = getUnsafe [ "defaultSpringStiffness" ]

_epsilonDistance :: ForceDirectedLayout_ -> Number
_epsilonDistance = getUnsafe [ "epsilonDistance" ]

_infinityDistance :: ForceDirectedLayout_ -> Number
_infinityDistance = getUnsafe [ "infinityDistance" ]

_maxIterations :: ForceDirectedLayout_ -> Number
_maxIterations = getUnsafe [ "maxIterations" ]

_moveLimit :: ForceDirectedLayout_ -> Number
_moveLimit = getUnsafe [ "moveLimit" ]

_setsPortSpots :: ForceDirectedLayout_ -> Boolean
_setsPortSpots = getUnsafe [ "setsPortSpots" ]

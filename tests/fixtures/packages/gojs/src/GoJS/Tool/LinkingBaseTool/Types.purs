module GoJS.Tool.LinkingBaseTool.Types where

import GoJS.Tool.Types (class IsTool, LinkingTool_, RelinkingTool_)

class IsTool t <= IsLinkingBaseTool t
instance IsLinkingBaseTool LinkingTool_
instance IsLinkingBaseTool RelinkingTool_
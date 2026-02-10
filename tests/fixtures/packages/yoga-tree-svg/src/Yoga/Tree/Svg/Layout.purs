module Yoga.Tree.Svg.Layout where

import Prelude


import Data.Set (Set)
import Data.Set (fromFoldable) as Set

import Play (Play, (~*))
import Play as Play


data Element
    = Breadcrumbs -- CurrentPaths
    | PreviewOrSelection -- hover preview || selection
    | History
    | Pinned
    | Export
    | Hints
    | ZoomControls
    | FoldTreeOrEdit
    | Graph


derive instance Eq Element
derive instance Ord Element


all :: Set Element
all = Set.fromFoldable [ Breadcrumbs, PreviewOrSelection, History, Pinned, Export, Hints, ZoomControls, FoldTreeOrEdit, Graph ]


data LayoutItem
    = E Element
    | S String


layout :: { width :: Number, height :: Number } -> Play LayoutItem
layout { width, height } =
    let
        graphWProp = (1.0 / 4.0) * 2.5
        breadcrumbsHeight = 90.0
        zoomInfoWidth = 300.0
        selectionHeight = 60.0
        exportHeight = 250.0
        graphWidth  = width  * graphWProp
        hintsHeight = 170.0
    in
    Play.i (S "background")
        ~* Play.width  width
        ~* Play.height height
        ~* Play.topToBottom
        ~* Play.with
            [ Play.i (S "top bar")
                ~* Play.widthGrow
                ~* Play.heightFit
                ~* Play.leftToRight
                ~* Play.with
                    [ Play.i (E Breadcrumbs)
                        ~* Play.widthGrow
                        ~* Play.height breadcrumbsHeight
                    , Play.i (E ZoomControls)
                        ~* Play.width zoomInfoWidth
                        ~* Play.heightGrow
                    ]
            , Play.i (S "middle section")
                ~* Play.widthGrow
                ~* Play.heightGrow
                ~* Play.leftToRight
                ~* Play.with
                    [ Play.i (E Graph)
                        ~* Play.width graphWidth
                        ~* Play.heightGrow
                    , Play.i (S "fold + export")
                        ~* Play.widthGrow
                        ~* Play.heightGrow
                        ~* Play.topToBottom
                        ~* Play.with
                            [ Play.i (E FoldTreeOrEdit)
                                ~* Play.widthGrow
                                ~* Play.heightGrow
                            , Play.i (E Export)
                                ~* Play.widthGrow
                                ~* Play.height exportHeight
                            ]
                    , Play.i (S "sel + pinned + history")
                        ~* Play.widthGrow
                        ~* Play.heightGrow
                        ~* Play.topToBottom
                        ~* Play.with
                            [ Play.i (E PreviewOrSelection)
                                ~* Play.widthGrow
                                ~* Play.height selectionHeight
                            , Play.i (E Pinned)
                                ~* Play.widthGrow
                                ~* Play.heightGrow
                            , Play.i (E History)
                                ~* Play.widthGrow
                                ~* Play.heightGrow
                            , Play.i (E Hints)
                                ~* Play.widthGrow
                                ~* Play.height hintsHeight
                            ]
                    ]
            ]

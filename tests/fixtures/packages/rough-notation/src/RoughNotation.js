import { annotate, annotationGroup } from "rough-notation"

export const annotate_ = element => roughAnnotationType => config => () => {
  fullConfig = { ...config }
  fullConfig.type = roughAnnotationType
  return annotate(element, fullConfig)
}

export const show_ = annotation => () => annotation.show()

export const hide_ = annotation => () => annotation.hide()

export const remove_ = annotation => () => annotation.remove()

export const animationDuration_ = annotation => () => annotation.animationDuration

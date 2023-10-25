#! /bin/bash

exercify () {
  sed '
    /:= by$/, /^   *done$/ {/:= by$/!{/^   *done$/!{/^  /d;};};}
    /^  *have.* := by$/{d;}
    s=^\(   *\)done=\1sorry\n&=
    ' "${1}"
}

exme () {
  newPth="${1/.lean/_questions.lean}"
  echo ${newPth}
  exercify "${1}" > "${newPth}"
}

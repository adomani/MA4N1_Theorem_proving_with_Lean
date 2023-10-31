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

mkNew () {
  local tl="$(ls MA4N1_2023/L* | sed -n 's=MA4N1_2023/L0*\([0-9][0-9]*\)_.*=\1=p' | tail -1)"
  tl="$(printf '%02d' "$(( tl + 1 ))")"
  local file="$( printf 'MA4N1_2023/L%s_%s.lean' "${tl}" "${1// /_}" )"
  if [ -f "${file}" ]; then
    lcyan $'File' ; printf ' %s ' "${file}" ; lcyan $'already exists!\n'
  else
    { brown $'save to file '; printf '%s\n' "${file}" ; } >&2
    printf $'import Mathlib.Tactic\n\nnamespace TPwL\n\n\n\nend TPwL\n' > "${file}"
  fi
}

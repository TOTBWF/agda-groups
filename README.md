## Group Theory in Agda

A formalization of group theory in Agda, done with a categorical flourish.

## Design

This library does things in a highly categorical fashion. For instance
- Subgroups are defined via monomorphisms
- Normal Subgroups are defined via normal monomorphisms
- Kernels are defined using the categorical definition

However, it is useful to have a straightforward way of actually
constructing some of these objects. These are called the "Canonical"
structures by the library, and are usually filed under a Canonical
module somewhere.

## Notes

This repo is mainly a place for experimentation. A lot of the things
found here should probably be upstreamed at some point.

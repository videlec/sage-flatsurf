sage-flatsurf
=============

This is a software package for working with flat surfaces in
`SageMath`_. The flatsurf documentation
is available at http://www.labri.fr/perso/vdelecro/flatsurf/latest/

We aim for this package to support the investigation of geometric, algebraic and
dynamical questions related to flat surfaces. By flat surface we mean a surface
modeled on the plane with monodromy given by similarities of the plane, though
current efforts are focused on translation surfaces and half-translation
surfaces.

Currently, the package can generate images of flat surfaces, plot straight-line
trajectories, deform surfaces through the SL(2,R) action, and compute Delaunay
decompositions. `SageMath`_ is used to perform exact arithmetic.

This package is open source software, released under GPL v2 (see the ``COPYING``
file). We welcome any help to improve the package and especially to broaden
the package's mathematical abilities.

The package is currently in active development. If you would like assistance
in using it, please contact the authors.

Links
-----

* documentation: https://www.labri.fr/perso/vdelecro/sage-flatsurf/

* Python Package Index page: https://pypi.org/project/sage-flatsurf/

* development website: https://github.com/videlec/sage-flatsurf/

Installing the dependency
-------------------------

Our software depends on the `surface-dynamics`_ package,
which is distributed on PyPI. To install it, run the
following command::

    $ sage -pip install surface_dynamics [--user]

The --user option is optional and allows to install the corresponding
Python module in your user space rather than system-wide (and thus
does not require administrator rights).

Installing the package
----------------------

Since sage-flatsurf is available on PyPI at https://pypi.org/project/sage-flatsurf/,
the released version of sage-flatsurf can be installed by running the following command::

    $ sage -pip install sage-flatsurf [--user] [--upgrade]

To install the development version of sage-flatsurf, run instead::

    $ sage -pip install git+https://github.com/videlec/sage-flatsurf [--user] [--upgrade]

The options ``--user`` and ``--upgrade`` are optional. The option ``--user`` make
the installation in your home directory instead of in the Sage sources. The
option ``--upgrade`` allows you to upgrade if the package is already installed.

This might fail if `Git <https://git-scm.com/>`_ is not installed on your
computer (which could happen for example with certain versions of Sage in Windows).
In this situation you have two options. Either you install Git. Or you download
this project from the "Clone or download" drop-down menu above (you should get
a zip file). Then you need to run the command::

    $ sage -pip install TARBALL_NAME [--user] [--upgrade]

where ``TARBALL_NAME`` has to be replaced with the full path to your tarball.
Under Windows, it should be a Cygwin path and will look something like
``/cygdrive/c/Users/You/Downloads/sage-flatsurf-master.zip``.

Then you should be able to use the following within sage::

    sage: import flatsurf.geometry.similarity_surface_generators as sfg
    sage: T = sfg.translation_surfaces.regular_octagon()
    sage: T
    Translation surface built from 1 polygon
    sage: T.stratum()
    H_2(2)

To uninstall the package, you can do::

    $ sage -pip uninstall flatsurf

Run the tests
-------------

Running the tests of a specific file or directory is done by running::

    $ sage -t --force-lib ARG

where ``ARG`` is either a directory or file. In particular, to test all the
files in the module just do::

    $ sage -t --force-lib flatsurf

Tests on the master branch are automatically run through
`Travis-CI <https://travis-ci.org/videlec/sage-flatsurf?branch=master>`_.

Related projects
----------------

There are several related projects

* `surface-dynamics`_ (SageMath module): more focused on dynamics (interval
  exchanges)

* `veerer`_ (Python module): specific to handle specific triangulation of
  half-translation surfaces

* `flatsurf`_: (C++ library with Python interface) computing GL(2,R)-orbit
  closure of translation surfaces

Primary Contributors
--------------------

* Vincent Delecroix (Bordeaux)
* Pat Hooper (City College of New York and CUNY Graduate Center)

We welcome others to contribute.

Acknowledgements
----------------

* This software project was created during a thematic semester at
  `ICERM <https://icerm.brown.edu>`_.
* Hooper's contribution to the project has been supported by the National
  Science Foundation under Grant Number DMS-1500965. Any opinions, findings,
  and conclusions or recommendations expressed in this material are those of
  the authors and do not necessarily reflect the views of the National
  Science Foundation.
* Delecroix's contribution to the project has been supported by OpenDreamKit,
  Horizon 2020 European Research Infrastructures project #676541.

.. _SageMath: https://www.sagemath.org
.. _surface-dynamics: https://gitlab.com/videlec/surface_dynamics
.. _veerer: https://gitlab.com/videlec/veerer/
.. _flatsurf: https://github.com/flatsurf/

# BoostSRL - v1.1

Developed by [Jude Shavlik](http://pages.cs.wisc.edu/~shavlik/), [Tushar Khot](http://pages.cs.wisc.edu/~tushar/), [Sriraam Natarajan](http://utdallas.edu/~sxn177430/), and [members of the STARAI Lab](http://www.indiana.edu/~iustarai/people.html).

Contact: **Sriraam.Natarajan@utdallas.edu**

*BoostSRL (Boosting for Statistical Relational Models) is a gradient-boosting based approach to learning different types of SRL models.*

As with the standard gradient-boosting approach, our approach turns the model-learning problem to learning a sequence of regression models. The key difference to the standard approaches is that we learn relational regression models (i.e. regression models that operate on relational data). We assume the data to be in predicate-logic format and the output are essentially first-order regression trees where the inner nodes contain conjunctions of logical predicates.

---

| `Latest Release` | `License` | `Wiki` | `Website` | `Downloads` | `Datasets` |
| --- | --- | --- | --- | --- | --- |
| [![][release img]][release] | [![][license img]][license] | [BoostSRL Wiki](Home) | [Group Website](http://indiana.edu/~iustarai/) | [Downloads](https://github.com/boost-starai/BoostSRL-Misc/tree/master/VersionHistory/Version1.0) | [Datasets](https://github.com/boost-starai/BoostSRL-Misc/tree/master/Datasets) |

### New in Version 1.1

* Discretization of continuous variables
* Relational random walks (grounded and lifted)

## Getting Started

**Prerequisites**:

* Java (tested with *openjdk 1.8.0_144*)

**Installation**:

* Download stable jar file.  
* Download stable source with git.  
  `git clone -b master https://github.com/boost-starai/BoostSRL.git`
* Nightly builds with git.  
  `git clone -b development https://github.com/boost-starai/BoostSRL.git`
  
## Basic Usage

<img src="https://raw.githubusercontent.com/boost-starai/BoostSRL-Misc/master/Images/basicFileStructure.png" alt="Basic file structure for the Cora dataset which BoostSRL assumes for most operations." width="558" display="block" margin="auto">

BoostSRL assumes that data are contained in files with data structured in predicate-logic format.

    [~/BoostSRL/]$ java -jar v1-0.jar -l -train train/ -test test/ -target workedunder -trees 10


## Contributing

Please refer to [CONTRIBUTING.md](.github/CONTRIBUTING.md) for documentation on submitting issues and pull requests.

## Versioning

We use [Semantic Versioning (Major.Minor.Patch)](http://semver.org/) for versioning. See [Releases](https://github.com/boost-starai/BoostSRL/releases) for all stable versions that are available, associated documentation can be found via the changelog.

## Acknowledgements

[license]:license.txt
[release]:https://github.com/boost-starai/BoostSRL/releases
[license img]:https://img.shields.io/github/license/boost-starai/BoostSRL.svg
[release img]:https://img.shields.io/github/tag/boost-starai/BoostSRL.svg

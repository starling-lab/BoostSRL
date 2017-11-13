# Maintaining BoostSRL Documentation

by: [Alexander L. Hayes (batflyer)](https://github.com/batflyer)

Maintenance of electronic resources (including code and documentation) is the responsibility of all contributors. Without people maintaining digital resources, those resources trend toward oblivion.

<img src="https://imgs.xkcd.com/comics/digital_resource_lifespan.png">

This document defines the standard for how this maintenance should be performed. As an initial plea, please understand that *this guide defines the bare minimum*, going above and beyond is always a goal.

## Setting up a Documentation Environment

1. [Good comments explain why things are done not what is done.](https://codeburst.io/good-code-vs-bad-code-35624b4e91bc)
2. I will boldly postulate that **bad code with good documentation** is better than **good code with bad documentation.**
3. **Though shalt use version control.** Version control (when used correctly) can help you keep track of your changes over time. Good comments can help you understand your code when you go back to it, or when someone is maintaining your code ten years down the road.
4. All documentation shall be written in a consistent format. GitHub uses Markdown, so I will frame this from the perspective of writing in Markdown.

Great documentation should take multiple perspectives into account. Start by thinking about what level of understanding you possess.
  
`md5sum` and `sha256sum`:

```
[hayesall]$ md5sum IMDB.zip
[hayesall]$ sha256sum IMDB.zip
```

## Datasets

Datasets shall have a title followed by five sections: *Table of Contents*, *Overview*, *Download*, *Setup*, and *Modes*.

1. The title will be a discernable name which the dataset can be referred to with.

2. **Table of Contents** shall list the four (or more) subsequent sections. Markdown is below.

3. **Overview** shall be an overview of what the data represents, what can be learned from it, and what the source of the data is.

4. **Download** shall have:

  * A download link to a .zip file hosted on the BoostSRL-Misc repository.
  * An `md5sum` and a `sha256sum` of the .zip.

5. **Setup**

6. **Modes** displays the contents of the `_bk.txt`, so that they may be seen without having to be downloaded.

## Template:

```
# Title

[All Datasets](boost-starai/BoostSRL-Misc/tree/master/Datasets)

by: (author)

[<< Previous Page]() | [BoostSRL Wiki](Home) | [Next Page >>]()

---

### Table of Contents:

1. [Overview](#overview)
2. [Download](#download)
3. [Setup](#setup)
4. [Modes](#modes)

---

### Overview

(description)

Target:

* (target)

[Table of Contents](#table-of-contents) - [BoostSRL Wiki](#home)

---

### Download

Download: [https://github.com/boost-starai/BoostSRL-Misc/blob/master/Datasets/(data)/(data).zip?raw=true]((data).zip) (X.XX KB)

* `md5sum`: xxxxx
* `sha256sum`: xxxxx

[Table of Contents](#table-of-contents) - [BoostSRL Wiki](#home)

---

### Setup

Linux/Mac:

1. After downloading, unzip (data).zip
  `unzip (data).zip`
  
2. If you are using a jar file, move it to the t
```

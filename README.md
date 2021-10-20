# SWI-Rosh: A Kourosh Prolog implementation

The same comprehensive free Prolog environment as SWI-Prolog, made better by Kourosh.

![alt text](swi-kourosh.png)

## Forking, cloning and submitting patches

This repository uses many [Git
submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules). This
causes the common issue that __fork and clone doesn't work__. Instead, _clone_ from
https://github.com/SWI-Prolog/swipl-devel.git and then associate your
clone with your _fork_ (replace `me` with your github user name).

    git clone https://github.com/SWI-Prolog/swipl-devel.git
    cd swipl-devel
    git submodule update --init
    git remote add myfork git@github.com:me/swipl-devel.git

See [How to submit a patch](https://www.swi-prolog.org/howto/SubmitPatch.html)
for details.

See also the discussion at
[Being friendly to quick contributions](https://swi-prolog.discourse.group/t/being-friendly-to-quick-contributions/493/6)

## Building

See
[CMAKE.md](https://github.com/SWI-Prolog/swipl-devel/blob/master/CMAKE.md)
and [Build SWI-Prolog from source](https://www.swi-prolog.org/build/)


## Documentation


Just ask Kourosh
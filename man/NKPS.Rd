%to do: chapters 3,6 examples

\name{NKPS}
\alias{NKPS}
\alias{NKPS2}
\alias{nkps1}
\docType{data}
\title{Attitudes on sex roles and marriage, measurements clustered in families}
\description{
Netherlands Kinship Panel Study (NKPS), www.nkps.nl.
Netherlands Kinship Panel Study (NKPS), a unique in-depth large-scale study into (changing) kinship relationships covering
a large number of life domains (Dykstra et al., 2004).

The data are tabulated in Bergsma, Croon, and Hagenaars (2009, Table 2.8, 2.10, 2.11, 2.12).
In Sections 5.1 and 6.4.2 more variables of the same data set are used, and these have only 1797 observations with no missing values;
this set is available as \code{NKPS2}.

Sections 2.2.3, 3.2, 5.1, 6.4.2 in Bergsma, Croon and Hagenaars (2009)
}
\usage{
 data(NKPS)
 data(NKPS2)
}
\format{
  A data frame with 1884 observations on the following variables.
  \describe{
    \item{\code{C}}{Child's Gender (factor):
        1 = Son
        2 = Daughter
       }
    \item{\code{P}}{Parent's Gender (factor):
        1 = Father
        2 = Mother
       }
    \item{\code{CS}}{Child's sex role attitude (ordered):
        1 = Nontrad.
        2 = Mod. trad.
        3 = Trad.
       }
    \item{\code{PS}}{Parent's sex role attitude (ordered):
        1 = Nontrad.
        2 = Mod. trad.
        3 = Trad.
       }
    \item{\code{CM}}{Child's marriage attitude (ordered):
        1 = Nontrad.
        2 = Mod. trad.
        3 = Trad.
       }
    \item{\code{PM}}{Parent's marriage attitude (ordered):
        1 = Nontrad.
        2 = Mod. trad.
        3 = Trad.
       }
  }
}

\source{
Dykstra, et al. (2004)
}
\references{
 Examples in book: \url{http://stats.lse.ac.uk/bergsma/cmm/R\%20files/NKPS.R}

 Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
 \emph{Marginal models for dependent, clustered, and longitudinal categorical data.}
 New York: Springer.

 Dykstra, P. A. Kalmijn, M., Knijn, T. C. M., Komter, A. E., Liefboer, A. C., & Mulder, C. H. (2004).
 \emph{Codebook of the Netherlands Kinship Panel Study: A multi-actor, multi-method, panel study on solidarity, in family relationships. Wave 1}
 (Tech. Rep. No. NKPS Working Paper 1).
 The Hague, The Netherlands: NICI.

}

\examples{

data(NKPS)
attach(NKPS)

############################################################################################################
# Chapter 2

# Table 2.8
Table.2.8 <- array(NA,c(4,4,4)); k <- 0
for (i in levels(P)) for (j in levels(C)){
  k <- k+1
  Table.2.8[,,k] <- addmargins(t(table(NKPS[,c(3,4)] [C==j & P==i,])))
}
dimnames(Table.2.8) <- list(c(levels(PS),"Total"),c(levels(CS),"Total"),
                       c("Father-Son","Father-Daughter","Mother-Son","Mother-Daughter"))
Table.2.8

# Table 2.9
Table.2.9 <- cbind(table(PS),table(CS),table(c(CS[C=="Son"],PS[P=="Father"])),
                   table(c(CS[C=="Daughter"],PS[P=="Mother"])))
dimnames(Table.2.9)[[2]] <- c("Parent","Child","Men","Women")
addmargins(Table.2.9)[,-5]

# Table 2.10

# Table 2.11


########################################################
# Data
recAB = NKPS[,c(3,4)]
recPCAB = NKPS[,c(1,2,3,4)]
recA1A2B1B2 = NKPS[,c(3,4,5,6)]

# list of frequencies in table AB
nAB = c(t(ftable(recAB)))


########################################################
# table AB and GT
# at produces marginal distributions of A and B, or the 2x3 table GT; G = generation and T = attititude
at = MarginalMatrix(c("A", "B"), list(c("A"), c("B")), c(3, 3));
bt = ConstraintMatrix(c("G", "T"), list(c("G"), c("T")), c(2, 3));

model1 = list(bt, "log", at);

nkps1 = MarginalModelFit(recAB, model1,ShowParameters=TRUE,Labels=list(list("G",c("men","women")),"T"),CoefficientDimensions=c(2,3),ShowProgress=10)

}
\keyword{datasets}

\name{cmm-package}
\alias{cmm-package}
\alias{cmm}
\docType{package}

\title{
Categorical Marginal Models
}
\description{
Quite extensive package for maximum likelihood estimation and weighted least squares estimation of categorical marginal models (CMMs; e.g., Bergsma & Rudas, 2002; Bergsma, Croon and Hagenaars, 2009}
\details{
\tabular{ll}{
Package: \tab cmm\cr
Type: \tab Package\cr
Version: \tab 0.12 \cr
Date: \tab 2018-03-11\cr
License: \tab GPL (>= 2)\cr
}
The package contains principal functions for analyzing marginal models for categorical data.
All functions are illustrated using examples from the book Marginal Models for Dependent,
Clustered, and Longitudunal Categorical Data (Bergsma, Croon, & Hagenaars, 2009).

The package contains the following functions
 \code{\link{ConstraintMatrix}}
 \code{\link{DesignMatrix}}
 \code{\link{DirectSum}}
 \code{\link{JoinModels}}
 \code{\link{MarginalMatrix}}
 \code{\link{MarginalModelFit}}
 \code{\link{ModelStatistics}}
 \code{\link{SampleStatistics}}
 \code{\link{SpecifyCoefficient}}

The package contains the following data sets
 \code{\link{Antisemitism}}
 \code{\link{BodySatisfaction}}
 \code{\link{ClarenceThomas}}
 \code{\link{DutchConcern}}
 \code{\link{DutchPolitics}}
 \code{\link{ErieCounty}}
 \code{\link{EVS}}
 \code{\link{GSS93}}
 \code{\link{LaborParticipation}}
 \code{\link{MarihuanaAlcohol}}
 \code{\link{NES}}
 \code{\link{NKPS}}
 \code{\link{NKPS2}}
 \code{\link{Smoking}}
}
\author{
Wicher P. Bergsma
Maintainer: L. Andries van der Ark \email{L.A.vanderArk@uva.nl}.
}

\references{
  Bergsma, W. P. (1997).
  \emph{Marginal models for categorical data}.
  Tilburg, The Netherlands: Tilburg University Press.
  \url{http://stats.lse.ac.uk/bergsma/pdf/bergsma_phdthesis.pdf}

  Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
  Marginal models for dependent, clustered, and longitudunal categorical data.
  Berlin: Springer. <DOI: 10.1007/b12532>

  Bergsma, W. P.& Rudas T. (2002). Marginal models for categorical data.
  \emph{The Annals of Statistics, 30}, 1, 140-159. 
  \url{ http://www.jstor.org/stable/2700006}
}

\keyword{package}

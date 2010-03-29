\name{SampleStatistics}
\alias{SampleStatistics}
\title{SampleStatistics}

\description{Gives sample values, standard errors and z-scores of one or more
coefficients. \code{SampleStatistics(dat,coeff)} gives exactly the same output as \code{ModelStatistics(dat,dat,"SaturatedModel",coeff)}. 
}

\usage{SampleStatistics(dat, coeff, CoefficientDimensions="Automatic",
    Labels="Automatic", ShowCoefficients=TRUE, ParameterCoding="Effect", ShowParameters=FALSE, ShowCorrelations=FALSE,  Title="")}

\arguments{
\item{dat}{observed data as a list of frequencies or as a data frame}
\item{coeff}{list of coefficients, can be obtained using \code{\link{SpecifyCoefficient}}, or a predefined function such as \code{"log"}}
\item{CoefficientDimensions}{numeric vector of dimensions of the table in which the coefficient vector is to be arranged}
\item{Labels}{list of characters or numbers indicating labels for dimensions of table in which the coefficient vector is to be arranged}
\item{ShowCoefficients}{boolean, indicating whether or not the coefficients are to be displayed}
\item{ShowParameters}{boolean, indicating whether or not the parameters (computed from the coefficients) are to be displayed}
\item{ParameterCoding}{Coding to be used for parameters, choice of \code{"Effect"}, \code{"Dummy"} and  \code{"Polynomial"}}
\item{ShowCorrelations}{boolean, indicating whether or not to show the correlation matrix for the estimated coefficients}
\item{Title}{title of computation to appear at top of screen output}
}

\details{
The data can be a data frame or vector of frequencies. \code{MarginalModelFit} converts a data frame \code{dat} using \code{c(t(ftable(dat)))}.

For \code{ParameterCoding}, the default for \code{"Dummy"} is that the first cell in the table is the reference cell. Cell
\eqn{(i,j,k,...)}{(i, j, k, ...)} can be made reference cell using \code{list("Dummy",c(i,j,k,...))}.
For \code{"Polynomial"} the default is to use centralized scores based on equidistant (distance 1)
linear scores, for example, if for \eqn{i=1,2,3,4}{i = 1, 2, 3, 4},
\deqn{\mu_i=\alpha+q_i\beta+r_i\gamma+s_i\delta}{mu_i = alpha + q_i beta + r_i gamma + s_i delta} where
\eqn{\beta}{beta} is a quadratic, \eqn{\gamma}{gamma} a cubic and \eqn{\delta}{delta} a quartic effect,
then \eqn{q_i}{q_i} takes the values \eqn{(-1.5,-.5,.5,1.5)}{(-1.5, -.5, .5, 1.5)}, \eqn{r_i}{r_i}
takes the values \eqn{(1,-1,-1,1)}{(1, -1, -1, 1)} (centralized squares of the \eqn{q_i}{q_i}),
and \eqn{s_i}{s_i} takes the values \eqn{(-3.375,-.125,.125,3.375)}{(-3.375, -.125, .125, 3.375)} (cubes of the \eqn{q_i}{q_i}).
}

\value{
A subset of the output of \code{MarginalModelFit}.
}

\references{
  Bergsma, W. P. (1997).
  \emph{Marginal models for categorical data}.
  Tilburg, The Netherlands: Tilburg University Press.
  \url{http://stats.lse.ac.uk/bergsma/pdf/bergsma_phdthesis.pdf}

  Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
  Marginal models for dependent, clustered, and longitudunal categorical data.
  Berlin: Springer.
}


\author{
 W. P. Bergsma \email{w.p.bergsma@lse.ac.uk}
}

\seealso{
\code{\link{ModelStatistics}}, \code{\link{MarginalModelFit}}
}

\examples{
 data(BodySatisfaction)

 ## Table 2.6 in Bergsma, Croon and Hagenaars (2009). Loglinear parameters for marginal table IS
 ## We provide two to obtain the parameters

 dat   <- BodySatisfaction[,2:8]        # omit first column corresponding to gender

 # matrix producing 1-way marginals, ie the 7x5 table IS
 at75 <- MarginalMatrix( c(1, 2, 3, 4, 5, 6, 7), list(c(1),c(2),c(3),c(4),c(5),c(6),c(7)), c(5, 5, 5, 5, 5, 5, 5) )

 # First method: the "coefficients" are the log-probabilities, from which all the (loglinear) parameters are calculated
 stats = SampleStatistics(dat, list("log",at75), CoefficientDimensions=c(7,5),Labels=c("I","S"),ShowCoefficients=FALSE,ShowParameters=TRUE)

 # Second method: the "coefficients" are explicitly specified as being the (highest-order) loglinear parameters
 loglinpar75 <- SpecifyCoefficient("LoglinearParameters", c(7,5) )
 stats = SampleStatistics(dat, list(loglinpar75, at75), CoefficientDimensions=c(7,5), Labels=c("I","S"))
}
\keyword{univar}

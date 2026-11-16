import PlattPointSubsetKernel
import PlattPointPackets.S3B000227
import PlattPointPackets.S3B000228
import PlattPointPackets.S3B000229
import PlattPointPackets.S3B000230
import PlattPointPackets.S3B000231
import PlattPointPackets.S3B000232
import PlattPointPackets.S3B000233
import PlattGlobalGrid.S7B000106
namespace ChenEffective.PlattWindow.PointCovers.S7B000106
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000227.points ++ ChenEffective.PlattWindow.PointPackets.S3B000228.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000229.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000230.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000231.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000232.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000233.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000106.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000106.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000106

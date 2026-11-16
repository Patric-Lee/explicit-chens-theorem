import PlattPointSubsetKernel
import PlattPointPackets.S3B000269
import PlattPointPackets.S3B000270
import PlattPointPackets.S3B000271
import PlattPointPackets.S3B000272
import PlattPointPackets.S3B000273
import PlattPointPackets.S3B000274
import PlattPointPackets.S3B000275
import PlattPointPackets.S3B000276
import PlattGlobalGrid.S7B000112
namespace ChenEffective.PlattWindow.PointCovers.S7B000112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000269.points ++ ChenEffective.PlattWindow.PointPackets.S3B000270.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000271.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000272.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000273.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000274.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000275.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000276.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000112.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000112.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000112

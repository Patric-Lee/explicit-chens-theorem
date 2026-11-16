import PlattPointSubsetKernel
import PlattPointPackets.S3B000262
import PlattPointPackets.S3B000263
import PlattPointPackets.S3B000264
import PlattPointPackets.S3B000265
import PlattPointPackets.S3B000266
import PlattPointPackets.S3B000267
import PlattPointPackets.S3B000268
import PlattPointPackets.S3B000269
import PlattGlobalGrid.S7B000111
namespace ChenEffective.PlattWindow.PointCovers.S7B000111
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000262.points ++ ChenEffective.PlattWindow.PointPackets.S3B000263.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000264.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000265.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000266.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000267.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000268.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000269.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000111.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000111.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000111

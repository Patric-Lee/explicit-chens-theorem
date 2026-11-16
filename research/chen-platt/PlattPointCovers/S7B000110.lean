import PlattPointSubsetKernel
import PlattPointPackets.S3B000254
import PlattPointPackets.S3B000255
import PlattPointPackets.S3B000256
import PlattPointPackets.S3B000257
import PlattPointPackets.S3B000258
import PlattPointPackets.S3B000259
import PlattPointPackets.S3B000260
import PlattPointPackets.S3B000261
import PlattPointPackets.S3B000262
import PlattGlobalGrid.S7B000110
namespace ChenEffective.PlattWindow.PointCovers.S7B000110
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((ChenEffective.PlattWindow.PointPackets.S3B000254.points ++ ChenEffective.PlattWindow.PointPackets.S3B000255.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000256.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000257.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000258.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000259.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000260.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000261.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000262.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000110.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000110.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000110

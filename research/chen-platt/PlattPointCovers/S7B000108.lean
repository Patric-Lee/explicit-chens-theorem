import PlattPointSubsetKernel
import PlattPointPackets.S3B000240
import PlattPointPackets.S3B000241
import PlattPointPackets.S3B000242
import PlattPointPackets.S3B000243
import PlattPointPackets.S3B000244
import PlattPointPackets.S3B000245
import PlattPointPackets.S3B000246
import PlattPointPackets.S3B000247
import PlattGlobalGrid.S7B000108
namespace ChenEffective.PlattWindow.PointCovers.S7B000108
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000240.points ++ ChenEffective.PlattWindow.PointPackets.S3B000241.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000242.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000243.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000244.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000245.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000246.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000247.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000108.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000108.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000108

import PlattPointSubsetKernel
import PlattPointPackets.S3B000233
import PlattPointPackets.S3B000234
import PlattPointPackets.S3B000235
import PlattPointPackets.S3B000236
import PlattPointPackets.S3B000237
import PlattPointPackets.S3B000238
import PlattPointPackets.S3B000239
import PlattPointPackets.S3B000240
import PlattGlobalGrid.S7B000107
namespace ChenEffective.PlattWindow.PointCovers.S7B000107
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000233.points ++ ChenEffective.PlattWindow.PointPackets.S3B000234.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000235.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000236.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000237.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000238.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000239.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000240.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000107.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000107.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000107

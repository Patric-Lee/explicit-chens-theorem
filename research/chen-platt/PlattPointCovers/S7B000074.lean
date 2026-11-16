import PlattPointSubsetKernel
import PlattPointPackets.S3B000033
import PlattPointPackets.S3B000034
import PlattPointPackets.S3B000035
import PlattPointPackets.S3B000036
import PlattPointPackets.S3B000037
import PlattPointPackets.S3B000038
import PlattGlobalGrid.S7B000074
namespace ChenEffective.PlattWindow.PointCovers.S7B000074
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S3B000033.points ++ ChenEffective.PlattWindow.PointPackets.S3B000034.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000035.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000036.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000037.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000038.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000074.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000074.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000074

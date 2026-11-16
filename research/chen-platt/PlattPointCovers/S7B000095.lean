import PlattPointSubsetKernel
import PlattPointPackets.S3B000154
import PlattPointPackets.S3B000155
import PlattPointPackets.S3B000156
import PlattPointPackets.S3B000157
import PlattPointPackets.S3B000158
import PlattPointPackets.S3B000159
import PlattPointPackets.S3B000160
import PlattPointPackets.S3B000161
import PlattGlobalGrid.S7B000095
namespace ChenEffective.PlattWindow.PointCovers.S7B000095
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000154.points ++ ChenEffective.PlattWindow.PointPackets.S3B000155.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000156.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000157.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000158.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000159.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000160.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000161.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000095.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000095.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000095

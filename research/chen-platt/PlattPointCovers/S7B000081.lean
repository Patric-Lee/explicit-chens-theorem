import PlattPointSubsetKernel
import PlattPointPackets.S3B000071
import PlattPointPackets.S3B000072
import PlattPointPackets.S3B000073
import PlattPointPackets.S3B000074
import PlattPointPackets.S3B000075
import PlattPointPackets.S3B000076
import PlattPointPackets.S3B000077
import PlattGlobalGrid.S7B000081
namespace ChenEffective.PlattWindow.PointCovers.S7B000081
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000071.points ++ ChenEffective.PlattWindow.PointPackets.S3B000072.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000073.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000074.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000075.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000076.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000077.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000081.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000081.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000081

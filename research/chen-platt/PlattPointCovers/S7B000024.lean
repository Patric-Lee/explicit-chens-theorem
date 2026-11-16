import PlattPointSubsetKernel
import PlattPointPackets.S2B000127
import PlattPointPackets.S2B000128
import PlattPointPackets.S2B000129
import PlattPointPackets.S2B000130
import PlattGlobalGrid.S7B000024
namespace ChenEffective.PlattWindow.PointCovers.S7B000024
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000127.points ++ ChenEffective.PlattWindow.PointPackets.S2B000128.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000129.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000130.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000024.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000024.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000024

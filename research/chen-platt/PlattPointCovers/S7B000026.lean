import PlattPointSubsetKernel
import PlattPointPackets.S2B000134
import PlattPointPackets.S2B000135
import PlattPointPackets.S2B000136
import PlattPointPackets.S2B000137
import PlattPointPackets.S2B000138
import PlattGlobalGrid.S7B000026
namespace ChenEffective.PlattWindow.PointCovers.S7B000026
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000134.points ++ ChenEffective.PlattWindow.PointPackets.S2B000135.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000136.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000137.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000138.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000026.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000026.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000026

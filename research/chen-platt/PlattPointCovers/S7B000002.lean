import PlattPointSubsetKernel
import PlattPointPackets.S2B000055
import PlattPointPackets.S2B000056
import PlattPointPackets.S2B000057
import PlattPointPackets.S2B000058
import PlattGlobalGrid.S7B000002
namespace ChenEffective.PlattWindow.PointCovers.S7B000002
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000055.points ++ ChenEffective.PlattWindow.PointPackets.S2B000056.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000057.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000058.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000002.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000002.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000002

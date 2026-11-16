import PlattPointSubsetKernel
import PlattPointPackets.S2B000149
import PlattPointPackets.S2B000150
import PlattPointPackets.S2B000151
import PlattPointPackets.S2B000152
import PlattGlobalGrid.S7B000030
namespace ChenEffective.PlattWindow.PointCovers.S7B000030
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000149.points ++ ChenEffective.PlattWindow.PointPackets.S2B000150.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000151.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000152.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000030.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000030.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000030

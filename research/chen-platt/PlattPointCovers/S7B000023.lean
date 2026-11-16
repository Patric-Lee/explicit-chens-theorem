import PlattPointSubsetKernel
import PlattPointPackets.S2B000123
import PlattPointPackets.S2B000124
import PlattPointPackets.S2B000125
import PlattPointPackets.S2B000126
import PlattPointPackets.S2B000127
import PlattGlobalGrid.S7B000023
namespace ChenEffective.PlattWindow.PointCovers.S7B000023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000123.points ++ ChenEffective.PlattWindow.PointPackets.S2B000124.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000125.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000126.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000127.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000023.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000023.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000023

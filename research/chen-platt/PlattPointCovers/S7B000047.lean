import PlattPointSubsetKernel
import PlattPointPackets.S2B000217
import PlattPointPackets.S2B000218
import PlattPointPackets.S2B000219
import PlattPointPackets.S2B000220
import PlattPointPackets.S2B000221
import PlattGlobalGrid.S7B000047
namespace ChenEffective.PlattWindow.PointCovers.S7B000047
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000217.points ++ ChenEffective.PlattWindow.PointPackets.S2B000218.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000219.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000220.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000221.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000047.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000047.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000047

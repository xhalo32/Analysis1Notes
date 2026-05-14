import time, curses, asyncio, sys
from curses import panel

from leanclient import LeanLSPClient
from watchdog.events import FileSystemEvent, FileSystemEventHandler, FileModifiedEvent
from watchdog.observers import Observer

def within_range(range, line):
    return range['start']['line'] <= line and line <= range['end']['line']

def collides(range1, range2):
    return within_range(range1, range2['start']['line']) or within_range(range1, range2['end']['line'])

def walk_symbols(symbols):
    res = []
    for sym in symbols:
        if 'children' in sym:
            res += walk_symbols(sym['children'])
        elif sym['kind'] == 6:
            res.append({
                'name': sym['name'],
                'range': sym['range']
            })
    return res

def get_declarations(client):
    diags = client.get_diagnostics()
    symbols = walk_symbols(client.get_document_symbols())
    for sym in symbols:
        for diag in diags:
            if collides(sym['range'], diag['range']):
                sym['message'] = diag['message'][0:25].replace('\n', ' ')
                sym['severity'] = diag['severity']
    return symbols

# https://gist.github.com/mivade/f4cb26c282d421a62e8b9a341c7c65f6
class _EventHandler(FileSystemEventHandler):
    def __init__(self, queue: asyncio.Queue, loop: asyncio.BaseEventLoop):
        self._loop = loop
        self._queue = queue
        super()

    def on_any_event(self, event: FileSystemEvent) -> None:
        self._loop.call_soon_threadsafe(self._queue.put_nowait, event)

class App:
    def __init__(self, stdscreen, name, client, queue):
        self.screen = stdscreen
        self.name = name
        self.client = client
        self.queue = queue
        self.symbols = []
        self.minibuffer = ""
        self.scroll = 0

    def draw_minibuffer(self):
        maxy, maxx = self.screen.getmaxyx()
        self.screen.addstr(maxy-2, 1, self.minibuffer)
    
    def write_minibuffer(self, message):
        self.minibuffer = message
        self.draw_minibuffer()
        self.display()

    async def handle_event(self, event):
        if isinstance(event, FileModifiedEvent):
            self.client.open_file()
            self.write_minibuffer("open_file")
            self.symbols = get_declarations(self.client)
            self.write_minibuffer("get_declarations")
            self.display()

    def max_name_len(self):
        if len(self.symbols):
            return max(map(lambda sym: len(sym['name']), self.symbols))
        else:
            return 0

    def max_message_len(self):
        if len(self.symbols):
            return max(map(lambda sym: len(sym.get('message', "")), self.symbols))
        else:
            return 0

    def display(self):
        msg2 = "Press 'q' to exit"

        maxy, maxx = self.screen.getmaxyx()
        self.screen.erase()

        self.screen.box()
        self.screen.addstr(
            1, int((maxx - len(self.name)) / 2), self.name
        )

        maxnamelen = self.max_name_len()
        maxmsglen = 25 # hard-coded to avoid jumping left and right
        maxwidth = 3 + 2 + maxnamelen + 2 + maxmsglen

        i = self.scroll
        for sym in self.symbols:
            i += 1
            y = i + 2
            x = int((maxx - maxwidth) / 2)
            if y <= 1 or y >= maxy - 1:
                continue
            line = sym['range']['start']['line']
            if 'severity' in sym and sym['severity'] < 3:
                self.screen.addstr(
                    y, x, f"{line+1:>3}: {sym['name']:>{maxnamelen}}: {sym['message']}", curses.color_pair(sym['severity']) | curses.A_BOLD
                )
            else:
                self.screen.addstr(
                    y, x, f"{line+1:>3}: {sym['name']:>{maxnamelen}}: all goals completed!", curses.color_pair(3) | curses.A_BOLD
                )

        self.draw_minibuffer()        
        self.screen.refresh()

    def adjust_scroll(self, amount):
        self.scroll += amount
        self.scroll = max(self.scroll, -len(self.symbols))
        self.scroll = min(self.scroll, 0)

    async def run(self):
        curses.curs_set(0)
        self.screen.nodelay(True)
        self.display()

        while True:
            key = self.screen.getch()

            if key == curses.ERR:
                if not self.queue.empty():
                    await self.handle_event(await self.queue.get())
                else:
                    await asyncio.sleep(0.1)
            elif key == curses.KEY_RESIZE:
                self.display()
            elif key in [curses.KEY_ENTER, ord("\n")]:
                print("enter")
            elif key == curses.KEY_UP:
                self.adjust_scroll(1)
                self.display()
            elif key == curses.KEY_DOWN:
                self.adjust_scroll(-1)
                self.display()
            elif key == ord("q"):
                break

        self.screen.clear()
        curses.doupdate()

def watch(queue, loop, file_path) -> None:
    handler = _EventHandler(queue, loop)

    observer = Observer()
    observer.schedule(handler, file_path)
    observer.start()
    observer.join(10)
    loop.call_soon_threadsafe(queue.put_nowait, None)

def app(stdscreen, queue, file_path):
    client = LeanLSPClient('.')
    sfc = client.create_file_client(file_path) # TODO lean server takes 100% cpu
    app = App(stdscreen, file_path, sfc, queue)
    asyncio.run(app.run())

def main(stdscreen):
    file_path = sys.argv[1]
    curses.start_color()
    curses.use_default_colors()
    curses.init_pair(1, curses.COLOR_RED, -1)
    curses.init_pair(2, curses.COLOR_YELLOW, -1)
    curses.init_pair(3, curses.COLOR_GREEN, -1)
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    queue = asyncio.Queue()

    futures = [
        loop.run_in_executor(None, watch, queue, loop, file_path),
        loop.run_in_executor(None, app, stdscreen, queue, file_path),
    ]

    loop.run_until_complete(asyncio.gather(*futures))

if __name__=='__main__':
    if len(sys.argv) != 2:
        print("Usage: lean_tui.py PATH")
        sys.exit(1)
    curses.wrapper(main)
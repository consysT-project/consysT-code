const socket = new WebSocket("ws://localhost:9999");
const documentList = document.getElementById("document-list");
const documentHeadline = document.getElementById("document-headline");
const documentCreateButton = document.getElementById("document-create-button");

function fetchDocuments() {
  socket.send(
    JSON.stringify({
      type: "fetchDocuments",
    })
  );

  socket.addEventListener("message", (event) => {
    const message = JSON.parse(event.data);
    if (message.type === "documentList") {
      message.documents.forEach((document) => {
        const li = document.createElement("li");
        const button = document.createElement("button");
        button.innerText = document.name;
        button.addEventListener("click", () => {
          showDocumentEditor(document.id);
        });
        li.appendChild(button);
        documentList.appendChild(li);
      });
    }
  });
}

function showDocumentEditor(title) {
  documentHeadline.innerText = "Edit document: " + title;
  documentList.style.display = "none";
  documentCreateButton.style.display = "none";

  const textarea = document.createElement("textarea");
  textarea.classList.add("form-control");
  textarea.style.height = "20vh";
  textarea.value = "Loading...";

  const backButton = document.createElement("button");
  backButton.classList.add("btn", "btn-secondary", "me-2");
  backButton.innerText = "Back";
  backButton.addEventListener("click", () => {
    documentHeadline.innerText = "Documents";
    documentList.style.display = "block";
    documentCreateButton.style.display = "block";
    documentEditor.style.display = "none";
  });

  const saveButton = document.createElement("button");
  saveButton.classList.add("btn", "btn-primary", "ml-2");
  saveButton.innerText = "Save";
  saveButton.addEventListener("click", () => {
    documentHeadline.innerText = "Documents";
    documentList.style.display = "block";
    documentCreateButton.style.display = "block";
    documentEditor.style.display = "none";
    saveDocument(title, textarea.value);

    const alert = document.createElement("div");
    alert.classList.add("alert", "alert-success", "mt-3");
    alert.setAttribute("role", "alert");
    alert.innerText = "Document saved successfully!";
    documentList.prepend(alert);

    // Remove the notification after 3 seconds
    setTimeout(() => {
      alert.remove();
    }, 3000);
  });

  const documentEditor = document.createElement("div");
  documentEditor.appendChild(textarea);

  const buttonWrapper = document.createElement("div");
  buttonWrapper.classList.add("d-flex", "justify-content-end", "my-4");
  buttonWrapper.appendChild(backButton);
  buttonWrapper.appendChild(saveButton);

  documentEditor.appendChild(buttonWrapper);

  document.body.appendChild(documentEditor);

  socket.addEventListener("message", (event) => {
    const message = JSON.parse(event.data);
    if (message.type === "readDocument" && message.title === title) {
      textarea.value = message.content;
    }
  });

  socket.send(
    JSON.stringify({
      type: "readDocument",
      title,
    })
  );
}

function createDocument() {
  const title = prompt("Enter a name for the new document:");
  if (!title) {
    return;
  }

  socket.send(
    JSON.stringify({
      type: "createDocument",
      title,
    })
  );

  // Add the document row
  const li = document.createElement("li");
  li.classList.add("list-group-item");

  const row = document.createElement("div");
  row.classList.add("row", "align-items-center");

  const titleCol = document.createElement("div");
  titleCol.classList.add("col-sm-10");
  titleCol.innerText = title;

  const buttonCol = document.createElement("div");
  buttonCol.classList.add("col-sm-2", "text-right");

  const button = document.createElement("button");
  button.innerText = "Edit";
  button.classList.add("btn", "btn-secondary");
  button.addEventListener("click", () => {
    showDocumentEditor(title);
  });

  buttonCol.appendChild(button);
  row.appendChild(titleCol);
  row.appendChild(buttonCol);
  li.appendChild(row);

  documentList.appendChild(li);

  const alert = document.createElement("div");
  alert.classList.add("alert", "alert-success", "mt-3");
  alert.setAttribute("role", "alert");
  alert.innerText = "Document created successfully!";
  documentList.prepend(alert);

  // Remove the notification after 3 seconds
  setTimeout(() => {
    alert.remove();
  }, 3000);
}

function saveDocument(title, content) {
  socket.send(
    JSON.stringify({
      type: "saveDocument",
      title,
      content,
    })
  );
}

socket.addEventListener("open", () => {
  console.log("WebSocket connection established");
  //fetchDocuments();
});

socket.addEventListener("close", () => {
  console.log("WebSocket connection closed");
});

socket.addEventListener("error", (error) => {
  console.error("WebSocket error:", error);
});
